package circuit.block;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import circuit.Circuit;
import circuit.exceptions.PlacementException;
import circuit.pin.AbstractPin;

import placers.SAPlacer.Swap;
import util.Triple;

public class TimingGraph implements Iterable<TimingGraph.TimingGraphEntry>, Serializable {

    private static final long serialVersionUID = 5056732903629079227L;

    private Circuit circuit;

    // A list of clock domains, along with their unique id and delay
    private Map<String, Integer> clocks = new HashMap<>();

    private transient ArrayList<LeafBlock> endPointBlocks;
    private transient List<LeafBlock> affectedBlocks;

    private double criticalityExponent;
    private transient double maxDelay;


    public TimingGraph(Circuit circuit) {
        this.circuit = circuit;
        this.initializeData();
    }

    private void readObject(ObjectInputStream in) throws ClassNotFoundException, IOException {
        in.defaultReadObject();
        this.initializeData();
    }

    private void initializeData() {
        this.endPointBlocks = new ArrayList<LeafBlock>();
        this.affectedBlocks = new ArrayList<LeafBlock>();
    }


    public void build() {

        for(LeafBlock block : this.circuit.getLeafBlocks()) {
            boolean isClocked = block.isClocked();

            if(isClocked) {
                this.endPointBlocks.add(block);

            } else {
                boolean isConstantGenerator = true;
                for(AbstractPin inputPin : block.getInputPins()) {
                    if(inputPin.getSource() != null) {
                        isConstantGenerator = false;
                        break;
                    }
                }

                if(isConstantGenerator) {
                    this.endPointBlocks.add(block);
                }
            }
        }

        for(LeafBlock block : this.circuit.getLeafBlocks()) {
            this.traverseFromSource(block);
        }
    }

    private void traverseFromSource(LeafBlock pathSource) {
        double setupDelay = this.getSetupTime(pathSource);

        LinkedList<Triple<Integer, AbstractPin, Double>> stack = new LinkedList<>();

        int sourcePinIndex = 0;
        for(AbstractPin outputPin : pathSource.getOutputPins()) {
            if(pathSource.isClocked()) {
                setupDelay += outputPin.getPortType().getSetupTime();
            }

            // Insert elements at the bottom of the stack, so that the output pins of
            // the source block will be processed in ascending order. This is necessary
            // for the method addSink().
            stack.addLast(new Triple<Integer, AbstractPin, Double>(sourcePinIndex, outputPin, setupDelay));

            sourcePinIndex++;
        }

        while(stack.size() > 0) {
            Triple<Integer, AbstractPin, Double> entry = stack.pop();
            int currentSourcePinIndex = entry.getFirst();
            AbstractPin currentPin = entry.getSecond();
            double currentDelay = entry.getThird();


            AbstractBlock owner = currentPin.getOwner();

            // The pin is the input of a leaf block, so a timing graph node
            if(currentPin.isInput() && owner.isLeaf()) {
                LeafBlock pathSink = ((LeafBlock) owner);

                double endDelay;
                if(owner.isClocked()) {
                    endDelay = currentPin.getPortType().getSetupTime();

                } else {
                    List<AbstractPin> outputPins = owner.getOutputPins();
                    endDelay = currentPin.getPortType().getDelay(outputPins.get(0).getPortType());
                }

                pathSource.addSink(currentSourcePinIndex, pathSink, currentDelay + endDelay);

            // The block has children: proceed with the sinks of the current pin
            } else {
                for(AbstractPin sinkPin : currentPin.getSinks()) {
                    if(sinkPin != null) {
                        double sourceSinkDelay = currentPin.getPortType().getDelay(sinkPin.getPortType());
                        double totalDelay = currentDelay + sourceSinkDelay;

                        stack.push(new Triple<Integer, AbstractPin, Double>(currentSourcePinIndex, sinkPin, totalDelay));
                    }
                }
            }
        }
    }

    private double getSetupTime(LeafBlock block) {
        List<AbstractPin> clockPins = block.getClockPins();
        if(clockPins.size() == 0) {
            return 0;
        }

        // A leaf block can only have 1 clock
        assert(clockPins.size() == 1);

        AbstractPin clockPin = clockPins.get(0);
        double delay = 0;

        while(true) {
            AbstractPin previousClockPin = clockPin.getSource();
            if(previousClockPin == null) {
                break;
            }

            delay += previousClockPin.getPortType().getDelay(clockPin.getPortType());
            clockPin = previousClockPin;
        }

        String clockName = clockPin.getOwner().getName();

        int clockDomain = -1;
        if(this.clocks.containsKey(clockName)) {
            clockDomain = this.clocks.get(clockName);
        } else {
            clockDomain = this.clocks.size();
            this.clocks.put(clockName, clockDomain);
        }

        block.setClockDomain(clockDomain);

        return delay;
    }


    public void setCriticalityExponent(double criticalityExponent) {
        this.criticalityExponent = criticalityExponent;
        this.calculateCriticalities();
    }


    public void reset() {
        for(LeafBlock block : this.circuit.getLeafBlocks()) {
            int numSinks = block.getNumSinks();
            for(int i = 0; i < numSinks; i++) {
                block.getSinkEdge(i).setWireDelay(0);
            }
        }
    }


    public void recalculateAllSlacksCriticalities(boolean recalculateWireDelays) {
        this.calculateArrivalTimes(recalculateWireDelays);
        this.calculateRequiredTimes();
        this.calculateCriticalities();
    }

    public void calculateArrivalTimes(boolean recalculateWireDelays) {
        for(LeafBlock block : this.circuit.getLeafBlocks()) {
            block.resetTiming();
            if(recalculateWireDelays) {
                block.calculateSinkWireDelays();
            }
        }

        Stack<LeafBlock> todo = new Stack<LeafBlock>();

        for(LeafBlock startBlock : this.endPointBlocks) {
            for(LeafBlock sink : startBlock.getSinks()) {
                sink.incrementProcessedSources();
                if(sink.allSourcesProcessed()) {
                    todo.add(sink);
                }
            }
        }


        this.maxDelay = 0;
        while(todo.size() > 0) {
            LeafBlock currentBlock = todo.pop();

            double arrivalTime = currentBlock.calculateArrivalTime();
            if(arrivalTime > this.maxDelay) {
                this.maxDelay = arrivalTime;
            }

            if(!currentBlock.isClocked()) {
                for(LeafBlock sink : currentBlock.getSinks()) {
                    sink.incrementProcessedSources();
                    if(sink.allSourcesProcessed()) {
                        todo.add(sink);
                    }
                }
            }
        }
    }

    public void calculateRequiredTimes() {
        Stack<LeafBlock> todo = new Stack<LeafBlock>();

        for(LeafBlock endBlock : this.endPointBlocks) {
            endBlock.setRequiredTime(this.maxDelay);

            for(LeafBlock source : endBlock.getSources()) {
                source.incrementProcessedSinks();
                if(source.allSinksProcessed()) {
                    todo.add(source);
                }
            }
        }

        while(todo.size() > 0) {
            LeafBlock currentBlock = todo.pop();

            if(!currentBlock.isClocked()) {
                currentBlock.calculateRequiredTime();

                for(LeafBlock source : currentBlock.getSources()) {
                    source.incrementProcessedSinks();
                    if(source.allSinksProcessed()) {
                        todo.add(source);
                    }
                }
            }
        }
    }

    public void calculateCriticalities() {
        for(LeafBlock block : this.circuit.getLeafBlocks()) {
            block.calculateCriticalities(this.maxDelay, this.criticalityExponent);
        }
    }

    public double getMaxDelay() {
        return this.maxDelay * Math.pow(10, 9);
    }

    public double calculateTotalCost() {
        double totalCost = 0;

        for(LeafBlock block : this.circuit.getLeafBlocks()) {
            totalCost += block.calculateCost();
        }

        return totalCost;
    }


    public double calculateDeltaCost(Swap swap) {
        double cost = 0;

        this.affectedBlocks.clear();


        // Switch the positions of the blocks
        try {
            swap.apply();
        } catch(PlacementException e) {
            e.printStackTrace();
        }

        int numBlocks = swap.getNumBlocks();
        for(int i = 0; i < numBlocks; i++) {
            GlobalBlock block1 = swap.getBlock1(i);
            GlobalBlock block2 = swap.getBlock2(i);

            if(block1 != null) {
                cost += this.calculateDeltaCost(block1, block2);
            }
            if(block2 != null) {
                cost += this.calculateDeltaCost(block2, block1);
            }
        }


        // Put the blocks back in their original position
        try {
            swap.undoApply();
        } catch(PlacementException e) {
            e.printStackTrace();
        }

        return cost;
    }

    private double calculateDeltaCost(GlobalBlock block1, GlobalBlock block2) {
        List<LeafBlock> nodes1 = block1.getLeafBlocks();
        this.affectedBlocks.addAll(nodes1);

        double cost = 0;
        for(LeafBlock node : nodes1) {
            cost += node.calculateDeltaCost(block2);
        }

        return cost;
    }

    public void pushThrough() {
        for(LeafBlock block : this.affectedBlocks) {
            block.pushThrough();
        }
    }

    public void revert() {
        // Do nothing
    }



    // Iterator methods
    // When iterating over a TimingGraph object, you will get a TimingGraphEntry
    // object for each connection in the timinggraph. Each of those objects contains
    // a source block, a sink block and the criticality of the connection.
    @Override
    public Iterator<TimingGraphEntry> iterator() {
        return new TimingGraphIterator(this.circuit.getGlobalBlocks());
    }

    private class TimingGraphIterator implements Iterator<TimingGraphEntry> {

        private GlobalBlock sourceGlobalBlock;
        private Iterator<GlobalBlock> sourceGlobalBlockIterator;

        private LeafBlock sourceBlock;
        private Iterator<LeafBlock> sourceBlockIterator;

        private int maxSinkIndex, sinkIndex;

        private TimingGraphEntry cachedEntry = null;


        TimingGraphIterator(List<GlobalBlock> globalBlocks) {
            this.sourceGlobalBlockIterator = globalBlocks.iterator();

            this.sourceGlobalBlock = this.sourceGlobalBlockIterator.next();
            this.sourceBlockIterator = this.sourceGlobalBlock.getLeafBlocks().iterator();

            this.sourceBlock = this.sourceBlockIterator.next();
            this.maxSinkIndex = this.sourceBlock.getNumSinks();
            this.sinkIndex = 0;
        }

        @Override
        public boolean hasNext() {
            if(this.cachedEntry != null) {
                return true;
            }

            while(this.sinkIndex < this.maxSinkIndex) {

                while(!this.sourceBlockIterator.hasNext()) {
                    if(!this.sourceGlobalBlockIterator.hasNext()) {
                        return false;
                    }

                    this.sourceGlobalBlock = this.sourceGlobalBlockIterator.next();
                    this.sourceBlockIterator = this.sourceGlobalBlock.getLeafBlocks().iterator();
                }

                this.sourceBlock = this.sourceBlockIterator.next();
                this.maxSinkIndex = this.sourceBlock.getNumSinks();
                this.sinkIndex = 0;
            }

            LeafBlock sink = this.sourceBlock.getSink(this.sinkIndex);
            TimingEdge edge = this.sourceBlock.getSinkEdge(this.sinkIndex);
            this.sinkIndex++;

            this.cachedEntry = new TimingGraphEntry(
                    this.sourceGlobalBlock,
                    sink.getGlobalParent(),
                    edge.getCriticality(),
                    this.sourceBlock.getNumSinks());

            return true;
        }

        @Override
        public TimingGraphEntry next() {
            TimingGraphEntry entry = this.cachedEntry;
            this.cachedEntry = null;
            return entry;
        }

        @Override
        public void remove() {
            // Not supported
        }
    }

    class TimingGraphEntry {
        private GlobalBlock source;
        private GlobalBlock sink;
        private double criticality;
        private int numSinks;

        TimingGraphEntry(GlobalBlock source, GlobalBlock sink, double criticality, int numSinks) {
            this.source = source;
            this.sink = sink;
            this.criticality = criticality;
            this.numSinks = numSinks;
        }

        public GlobalBlock getSource() {
            return this.source;
        }
        public GlobalBlock getSink() {
            return this.sink;
        }
        public double getCriticality() {
            return this.criticality;
        }
        public int getNumSinks() {
            return this.numSinks;
        }
    }
}
