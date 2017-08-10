package place.placers.analytical;

import place.circuit.Circuit;
import place.circuit.architecture.BlockCategory;
import place.circuit.architecture.BlockType;
import place.circuit.block.GlobalBlock;
import place.interfaces.Logger;
import place.interfaces.Options;
import place.visual.PlacementVisualizer;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

public abstract class GradientPlacer extends LiquidPlacer {

    private static final String
        O_LEARNING_RATE_START = "learning rate start",
        O_LEARNING_RATE_STOP = "learning rate stop",

        O_MAX_CONN_LENGTH_RATIO_SPARSE = "max conn length ratio sparse",
        O_MAX_CONN_LENGTH_DENSE = "max conn length dense",

        O_BETA1 = "beta1",
        O_BETA2 = "beta2",
        O_EPS = "eps",

        O_OUTER_EFFORT_LEVEL = "outer effort level",
        O_INNER_EFFORT_LEVEL = "inner effort level";

    public static void initOptions(Options options) {
        LiquidPlacer.initOptions(options);

        options.add(
                O_LEARNING_RATE_START,
                "ratio of distance to optimal position that is moved",
                new Double(1));

        options.add(
                O_LEARNING_RATE_STOP,
                "ratio of distance to optimal position that is moved",
                new Double(0.01));

        options.add(
                O_MAX_CONN_LENGTH_RATIO_SPARSE,
                "maximum connection length in sparse placement is ratio of circuit width",
                new Double(0.25));

        options.add(
                O_MAX_CONN_LENGTH_DENSE,
                "maximum connection length in dense placement",
                new Integer(30));

        options.add(
                O_BETA1,
                "adam gradient descent beta1 parameter",
                new Double(0.9));

        options.add(
                O_BETA2,
                "adam gradient descent beta2 parameter",
                new Double(0.999));

        options.add(
                O_EPS,
                "adam gradient descent eps parameter",
                new Double(10e-10));

        options.add(
                O_OUTER_EFFORT_LEVEL,
                "number of solve-legalize iterations",
                new Integer(10));

        options.add(
                O_INNER_EFFORT_LEVEL,
                "number of gradient steps to take in each outer iteration",
                new Integer(100));
    }

    private final double maxConnectionLength;
    protected double learningRate, learningRateMultiplier;
    private final double beta1, beta2, eps;

    private double latestCost, minCost;

    protected final int numIterations, effortLevel;

    // Only used by GradientPlacerTD
    protected double tradeOff; 
    protected List<CritConn> criticalConnections;

    protected Legalizer hardblockLegalizer;
    protected Legalizer labSpreader;
    protected Legalizer labLegalizer;

    protected LinearSolverGradient solver;

    private Map<BlockType, boolean[]> netMap;
    private boolean[] allTrue;
    private int[] netEnds;
    private int[] netBlockIndexes;
    private float[] netBlockOffsets;

    protected boolean[] fixed;

    public GradientPlacer(
            Circuit circuit,
            Options options,
            Random random,
            Logger logger,
            PlacementVisualizer visualizer){

        super(circuit, options, random, logger, visualizer);

    	this.effortLevel = this.options.getInteger(O_INNER_EFFORT_LEVEL);
    	this.numIterations = this.options.getInteger(O_OUTER_EFFORT_LEVEL) + 1;

        this.learningRate = this.options.getDouble(O_LEARNING_RATE_START);
        this.learningRateMultiplier = Math.pow(this.options.getDouble(O_LEARNING_RATE_STOP) / this.options.getDouble(O_LEARNING_RATE_START), 1.0 / (this.numIterations - 1.0));

        this.beta1 = this.options.getDouble(O_BETA1);
        this.beta2 = this.options.getDouble(O_BETA2);
        this.eps = this.options.getDouble(O_EPS);

        this.latestCost = Double.MAX_VALUE;
        this.minCost = Double.MAX_VALUE;

        if(this.circuit.dense()) {
        	this.maxConnectionLength = this.options.getInteger(O_MAX_CONN_LENGTH_DENSE);
        } else {
        	this.maxConnectionLength = this.circuit.getWidth() * this.options.getDouble(O_MAX_CONN_LENGTH_RATIO_SPARSE);
        }

        this.criticalConnections = new ArrayList<>();
    }

    protected abstract void initializeIteration(int iteration);

    @Override
    public void initializeData() {
        super.initializeData();

        this.startTimer(T_INITIALIZE_DATA);

        this.hardblockLegalizer = new HardblockConnectionLegalizer(
                this.circuit,
                this.blockTypes,
                this.blockTypeIndexStarts,
                this.coorX,
                this.coorY,
                this.heights,
                this.visualizer,
                this.nets,
                this.netBlocks);
        this.hardblockLegalizer.setQuality(0.001, 0.001, this.numIterations);
        
        this.labSpreader = new GradientLegalizer(
                this.circuit,
                this.blockTypes,
                this.blockTypeIndexStarts,
                this.coorX,
                this.coorY,
                this.heights,
                this.visualizer,
                this.nets,
                this.netBlocks);
        
        this.labLegalizer = new DetailedLegalizer(
                this.circuit,
                this.blockTypes,
                this.blockTypeIndexStarts,
                this.coorX,
                this.coorY,
                this.heights,
                this.visualizer,
                this.nets,
                this.netBlocks);

        // Juggling with objects is too slow (I profiled this,
        // the speedup is around 40%)
        // Build some arrays of primitive types
        int netBlockSize = 0;
        for(int i = 0; i < this.numRealNets; i++) {
            netBlockSize += this.nets.get(i).blocks.length;
        }


        this.allTrue = new boolean[this.numRealNets];
        Arrays.fill(this.allTrue, true);
        this.netMap = new HashMap<>();
        for(BlockType blockType:BlockType.getBlockTypes(BlockCategory.CLB)){
        	this.netMap.put(blockType, new boolean[this.numRealNets]);
        	Arrays.fill(this.netMap.get(blockType), false);
        }
        for(BlockType blockType:BlockType.getBlockTypes(BlockCategory.HARDBLOCK)){
        	this.netMap.put(blockType, new boolean[this.numRealNets]);
        	Arrays.fill(this.netMap.get(blockType), false);
        }
        for(BlockType blockType:BlockType.getBlockTypes(BlockCategory.IO)){
        	this.netMap.put(blockType, new boolean[this.numRealNets]);
        	Arrays.fill(this.netMap.get(blockType), false);
        }

        this.netEnds = new int[this.numRealNets];
        this.netBlockIndexes = new int[netBlockSize];
        this.netBlockOffsets = new float[netBlockSize];

        int netBlockCounter = 0;
        for(int netCounter = 0; netCounter < this.numRealNets; netCounter++) {
            Net net = this.nets.get(netCounter);

            for(NetBlock block : net.blocks) {
                this.netBlockIndexes[netBlockCounter] = block.blockIndex;
                this.netBlockOffsets[netBlockCounter] = block.offset;

                netBlockCounter++;

                this.netMap.get(block.blockType)[netCounter] = true;
            }

            this.netEnds[netCounter] = netBlockCounter;
        }

        this.fixed = new boolean[this.coorX.length];

        this.solver = new LinearSolverGradient(
                this.coorX,
                this.coorY,
                this.netBlockIndexes,
                this.netBlockOffsets,
                this.maxConnectionLength,
                this.fixed,
                this.beta1, 
                this.beta2, 
                this.eps);

        this.stopTimer(T_INITIALIZE_DATA);
    }

    @Override
    protected void optimizeHardblock(BlockType type){
    	Arrays.fill(this.fixed, false);
		for(BlockType blockType : BlockType.getBlockTypes(BlockCategory.IO)){
			this.fixBlockType(blockType);
		}

    	for(BlockType blockType : BlockType.getBlockTypes(BlockCategory.CLB)){
    		this.fixBlockType(blockType);
    	}
    	for(BlockType blockType : BlockType.getBlockTypes(BlockCategory.HARDBLOCK)){
    		if(!blockType.equals(type)){
    			this.fixBlockType(blockType);
    		}
    	}

		this.doSolveLinear(this.netMap.get(type));
    }
    @Override
    protected void legalizeHardblock(BlockType type){
        this.startTimer(T_LEGALIZE);
        this.hardblockLegalizer.legalize(type);
        this.stopTimer(T_LEGALIZE);
    }
    @Override
    protected void optimizeAll(){
    	Arrays.fill(this.fixed, false);
		for(BlockType blockType : BlockType.getBlockTypes(BlockCategory.IO)){
			this.fixBlockType(blockType);
		}
		this.doSolveLinear(this.allTrue);
    }
    @Override
    protected void optimizeLAB(){
    	BlockType lab = BlockType.getBlockTypes(BlockCategory.CLB).get(0);
    	
    	Arrays.fill(this.fixed, false);
		for(BlockType blockType : BlockType.getBlockTypes(BlockCategory.IO)){
			this.fixBlockType(blockType);
		}
    	for(BlockType blockType : BlockType.getBlockTypes(BlockCategory.HARDBLOCK)){
    			this.fixBlockType(blockType);
    	}

		this.doSolveLinear(this.netMap.get(lab));
    }
    @Override
    protected void spreadLAB(){
    	BlockType lab = BlockType.getBlockTypes(BlockCategory.CLB).get(0);
    	
    	this.startTimer(T_LEGALIZE);
    	this.labSpreader.legalize(lab);
    	this.stopTimer(T_LEGALIZE);
    }
    @Override
    protected void legalizeLAB(){
    	BlockType lab = BlockType.getBlockTypes(BlockCategory.CLB).get(0);
    	
    	this.startTimer(T_LEGALIZE);
    	this.labLegalizer.legalize(lab);
    	this.stopTimer(T_LEGALIZE);
    }

    private void fixBlockType(BlockType fixBlockType){
    	for(GlobalBlock block:this.netBlocks.keySet()){
    		if(block.getType().equals(fixBlockType)){
    			int blockIndex = this.netBlocks.get(block).getBlockIndex();
    			this.fixed[blockIndex] = true;
    		}
    	}
    }
    private void doSolveLinear(boolean[] processNets){
        for(int i = 0; i < this.effortLevel; i++) {
            this.solveLinearIteration(processNets);

            //this.visualizer.addPlacement(String.format("gradient descent step %d", i), this.netBlocks, this.solver.getCoordinatesX(), this.solver.getCoordinatesY(), -1);
        }
    }

    /*
     * Build and solve the linear system ==> recalculates linearX and linearY
     * If it is the first time we solve the linear system ==> don't take pseudonets into account
     */
    protected void solveLinearIteration(boolean[] processNets) {
        this.startTimer(T_BUILD_LINEAR);

        // Set value of alpha and reset the solver
        this.solver.initializeIteration(this.learningRate);

        // Process nets
        this.processNets(processNets);

        // Add pseudo connections
        //if(this.anchorWeight != 0.0) {
        //    // this.legalX and this.legalY store the solution with the lowest cost
        //    // For anchors, the last (possibly suboptimal) solution usually works better
        //    this.solver.addPseudoConnections(this.legalizer.getLegalX(), this.legalizer.getLegalY());
        //}

        this.stopTimer(T_BUILD_LINEAR);

        // Solve and save result
        this.startTimer(T_SOLVE_LINEAR);
        this.solver.solve();
        this.stopTimer(T_SOLVE_LINEAR);
    }

    protected void processNets(boolean[] processNet) {
        int numNets = this.netEnds.length;

        int netStart, netEnd = 0;
        for(int netIndex = 0; netIndex < numNets; netIndex++) {
            netStart = netEnd;
            netEnd = this.netEnds[netIndex];

        	if(processNet[netIndex]){
                this.solver.processNet(netStart, netEnd);
        	}
        }
    }

    @Override
    protected void addStatTitles(List<String> titles) {
        titles.add("it");
        titles.add("stepsize");
        titles.add("anneal Q");
        titles.add("max conn length");

        //Wirelength cost
        titles.add("BB linear");
        titles.add("BB legal");

        //Timing cost
        if(this.isTimingDriven()){
        	titles.add("max delay");
        }

        titles.add("best");
        titles.add("time (ms)");
        titles.add("crit conn");
        titles.add("overlap");
    }

    @Override
    protected void printStatistics(int iteration, double time, int overlap) {
        List<String> stats = new ArrayList<>();

        stats.add(Integer.toString(iteration));
        stats.add(String.format("%.3f", this.learningRate));
        stats.add(String.format("%.5f", this.hardblockLegalizer.getQuality()));
        stats.add(String.format("%.1f", this.maxConnectionLength));

        //Wirelength cost
        stats.add(String.format("%.0f", this.linearCost));
        stats.add(String.format("%.0f", this.legalCost));

        //Timing cost
        if(this.isTimingDriven()){
        	stats.add(String.format("%.4g", this.timingCost));
        }

        stats.add(this.latestCost == this.minCost ? "yes" : "");
        stats.add(String.format("%.0f", time*Math.pow(10, 3)));
        stats.add(String.format("%d", this.criticalConnections.size()));
        stats.add(String.format("%d", overlap));

        this.printStats(stats.toArray(new String[0]));
    }

    @Override
    protected int numIterations() {
    	return this.numIterations;
    }

    @Override
    protected boolean stopCondition(int iteration) {
    	return iteration + 1 >= this.numIterations;
    }
}
