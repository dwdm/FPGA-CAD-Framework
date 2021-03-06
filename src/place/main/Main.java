package place.main;

import place.circuit.Circuit;
import place.circuit.architecture.Architecture;
import place.circuit.architecture.ArchitectureCacher;
import place.circuit.architecture.BlockCategory;
import place.circuit.architecture.BlockType;
import place.circuit.architecture.ParseException;
import place.circuit.block.GlobalBlock;
import place.circuit.exceptions.InvalidFileFormatException;
import place.circuit.exceptions.PlacementException;
import place.circuit.io.BlockNotFoundException;
import place.circuit.io.IllegalSizeException;
import place.circuit.io.NetParser;
import place.circuit.io.PlaceDumper;
import place.circuit.io.PlaceParser;
import place.interfaces.Logger;
import place.interfaces.Options;
import place.interfaces.OptionsManager;
import place.interfaces.Logger.Stream;
import place.interfaces.Options.Required;
import place.placers.Placer;
import place.placers.simulatedannealing.EfficientBoundingBoxNetCC;
import place.util.Timer;
import place.visual.PlacementVisualizer;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.ManagementFactory;
import java.util.HashMap;
import java.util.Map;
import java.util.Random;

import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

public class Main {

    private long randomSeed;

    private String circuitName;
    private File blifFile, netFile, inputPlaceFile, partialPlaceFile, outputPlaceFile;
    private File architectureFile;

    private boolean useVprTiming;
    private String vprCommand;
    private File lookupDumpFile;

    private boolean visual;

    private Logger logger;
    private OptionsManager options;
    private PlacementVisualizer visualizer;


    private Map<String, Timer> timers = new HashMap<String, Timer>();
    private String mostRecentTimerName;
    private Circuit circuit;


    private static final String
        O_ARCHITECTURE = "architecture.xml",
        O_BLIF_FILE = "blif file",
        O_NET_FILE = "net file",
        O_INPUT_PLACE_FILE = "input place file",
        O_PARTIAL_PLACE_FILE = "partial place file",
        O_OUTPUT_PLACE_FILE = "output place file",
        O_VPR_TIMING = "vpr timing",
        O_VPR_COMMAND = "vpr command",
        O_LOOKUP_DUMP_FILE = "lookup dump file",
        O_VISUAL = "visual",
        O_RANDOM_SEED = "random seed";


    public static void initOptionList(Options options) {
        options.add(O_ARCHITECTURE, "", File.class);
        options.add(O_BLIF_FILE, "", File.class);

        options.add(O_NET_FILE, "(default: based on the blif file)", File.class, Required.FALSE);
        options.add(O_INPUT_PLACE_FILE, "if omitted the initial placement is random", File.class, Required.FALSE);
        options.add(O_PARTIAL_PLACE_FILE, "placement of a part of the blocks", File.class, Required.FALSE);
        options.add(O_OUTPUT_PLACE_FILE, "(default: based on the blif file)", File.class, Required.FALSE);

        options.add(O_VPR_TIMING, "Use vpr timing information", Boolean.TRUE);
        options.add(O_VPR_COMMAND, "Path to vpr executable", "./vpr");
        options.add(O_LOOKUP_DUMP_FILE, "Path to a vpr lookup_dump.echo file", File.class, Required.FALSE);

        options.add(O_VISUAL, "show the placed circuit in a GUI", Boolean.FALSE);
        options.add(O_RANDOM_SEED, "seed for randomization", new Long(1));
    }


    public Main(OptionsManager options) {
        this.options = options;
        this.logger = options.getLogger();

        this.parseOptions(options.getMainOptions());
    }

    private void parseOptions(Options options) {

        this.randomSeed = options.getLong(O_RANDOM_SEED);

        this.inputPlaceFile = options.getFile(O_INPUT_PLACE_FILE);
        this.partialPlaceFile = options.getFile(O_PARTIAL_PLACE_FILE);

        this.blifFile = options.getFile(O_BLIF_FILE);
        this.netFile = options.getFile(O_NET_FILE);
        this.outputPlaceFile = options.getFile(O_OUTPUT_PLACE_FILE);

        File inputFolder = this.blifFile.getParentFile();
        this.circuitName = this.blifFile.getName().replaceFirst("(.+)\\.blif", "$1");

        if(this.netFile == null) {
            this.netFile = new File(inputFolder, this.circuitName + ".net");
        }
        if(this.outputPlaceFile == null) {
            this.outputPlaceFile = new File(inputFolder, this.circuitName + ".place");
        }

        this.architectureFile = options.getFile(O_ARCHITECTURE);

        this.useVprTiming = options.getBoolean(O_VPR_TIMING);
        this.vprCommand = options.getString(O_VPR_COMMAND);
        this.lookupDumpFile = options.getFile(O_LOOKUP_DUMP_FILE);

        this.visual = options.getBoolean(O_VISUAL);


        // Check if all input files exist
        this.checkFileExistence("Blif file", this.blifFile);
        this.checkFileExistence("Net file", this.netFile);
        this.checkFileExistence("Input place file", this.inputPlaceFile);
        this.checkFileExistence("Partial place file", this.partialPlaceFile);

        this.checkFileExistence("Architecture file", this.architectureFile);
    }


    protected void checkFileExistence(String prefix, File file) {
        if(file == null) {
            return;
        }

        if(!file.exists()) {
            this.logger.raise(new FileNotFoundException(prefix + " " + file));

        } else if(file.isDirectory()) {
            this.logger.raise(new FileNotFoundException(prefix + " " + file + " is a director"));
        }
    }



    public void runPlacement() {
        String totalString = "Total flow took";
        this.startTimer(totalString);

        this.loadCircuit();
        this.logger.println();

        this.printNumBlocks();


        // Enable the visualizer
        this.visualizer = new PlacementVisualizer(this.logger);
        if(this.visual) {
            this.visualizer.setCircuit(this.circuit);
        }


        // Read the place file
        if(this.partialPlaceFile != null) {
            PlaceParser placeParser = new PlaceParser(this.circuit, this.partialPlaceFile);
            try {
                placeParser.iohbParse();
            } catch(IOException | BlockNotFoundException | PlacementException | IllegalSizeException error) {
                this.logger.raise("Something went wrong while parsing the partial place file", error);
            }
            this.options.insertRandomPlacer();
        }else if(this.inputPlaceFile != null){
            this.startTimer("Placement parser");
            PlaceParser placeParser = new PlaceParser(this.circuit, this.inputPlaceFile);
            try {
                placeParser.parse();
            } catch(IOException | BlockNotFoundException | PlacementException | IllegalSizeException error) {
                this.logger.raise("Something went wrong while parsing the place file", error);
            }
            this.stopTimer();
            this.printStatistics("Placement parser", false);
        }else{
        	this.options.insertRandomPlacer();
        }

        //Garbage collection
        System.gc();

        // Loop through the placers
        int numPlacers = this.options.getNumPlacers();
        for(int placerIndex = 0; placerIndex < numPlacers; placerIndex++) {
            this.timePlacement(placerIndex);
        }


        if(numPlacers > 0) {
            PlaceDumper placeDumper = new PlaceDumper(
                    this.circuit,
                    this.netFile,
                    this.outputPlaceFile,
                    this.architectureFile);

            try {
                placeDumper.dump();
            } catch(IOException error) {
                this.logger.raise("Failed to write to place file: " + this.outputPlaceFile, error);
            }
        }

        this.stopAndPrintTimer(totalString);

        this.printGCStats();

        this.visualizer.createAndDrawGUI();
    }




    private void loadCircuit() {
        ArchitectureCacher architectureCacher = new ArchitectureCacher(
                this.circuitName,
                this.netFile,
                this.architectureFile,
                this.useVprTiming,
                this.lookupDumpFile);
        Architecture architecture = architectureCacher.loadIfCached();
        boolean isCached = (architecture != null);

        // Parse the architecture file if necessary
        if(!isCached) {
            this.startTimer("Architecture parsing");
            architecture = new Architecture(
                    this.circuitName,
                    this.architectureFile,
                    this.blifFile,
                    this.netFile);

            try {
                architecture.parse();
            } catch(IOException | InvalidFileFormatException | InterruptedException | ParseException | ParserConfigurationException | SAXException error) {
                this.logger.raise("Failed to parse architecture file or delay tables", error);
            }

            if(this.useVprTiming) {
                try {
                    if(this.lookupDumpFile == null) {
                        architecture.getVprTiming(this.vprCommand);
                    } else {
                        architecture.getVprTiming(this.lookupDumpFile);
                    }

                } catch(IOException | InterruptedException | InvalidFileFormatException error) {
                    this.logger.raise("Failed to get vpr delays", error);
                }
            }

            this.stopAndPrintTimer();
        }

        // Parse net file
        this.startTimer("Net file parsing");
        try {
            NetParser netParser = new NetParser(architecture, this.circuitName, this.netFile);
            this.circuit = netParser.parse();
            this.logger.println(this.circuit.stats());

        } catch(IOException error) {
            this.logger.raise("Failed to read net file", error);
        }
        this.stopAndPrintTimer();


        // Cache the circuit for future use
        if(!isCached) {
            this.startTimer("Circuit caching");
            boolean success = architectureCacher.store(architecture);
            this.stopAndPrintTimer();

            if(!success) {
                this.logger.print(Stream.ERR, "Something went wrong while caching the architecture");
            }
        }
    }


    private void printNumBlocks() {
        int numLut = 0,
            numFf = 0,
            numClb = 0,
            numHardBlock = 0,
            numIo = 0;
        
        int numPLL = 0,
        	numM9K = 0, 
        	numM144K = 0, 
        	numDSP = 0;

        int numPins = 0;
        for(GlobalBlock block:this.circuit.getGlobalBlocks()){
        	numPins += block.numClockPins();
        	numPins += block.numInputPins();
        	numPins += block.numOutputPins();
        }
        for(BlockType blockType : BlockType.getBlockTypes()) {

            String name = blockType.getName();
            BlockCategory category = blockType.getCategory();
            int numBlocks = this.circuit.getBlocks(blockType).size();

            if(name.equals("lut")) {
                numLut += numBlocks;

            } else if(name.equals("ff") || name.equals("dff")) {
                numFf += numBlocks;

            } else if(category == BlockCategory.CLB) {
                numClb += numBlocks;

            } else if(category == BlockCategory.HARDBLOCK) {
                numHardBlock += numBlocks;
                
                if(blockType.equals(BlockType.getBlockTypes(BlockCategory.HARDBLOCK).get(0))){
                	numPLL += numBlocks;
                }else if(blockType.equals(BlockType.getBlockTypes(BlockCategory.HARDBLOCK).get(1))){
                	numDSP += numBlocks;
                }else if(blockType.equals(BlockType.getBlockTypes(BlockCategory.HARDBLOCK).get(2))){
                	numM9K += numBlocks;
                }else if(blockType.equals(BlockType.getBlockTypes(BlockCategory.HARDBLOCK).get(3))){
                	numM144K += numBlocks;
                }

            } else if(category == BlockCategory.IO) {
                numIo += numBlocks;
            }
        }

        this.logger.println("Circuit statistics:");
        this.logger.printf("   clb: %d\n      lut: %d\n      ff: %d\n   hardblock: %d\n      PLL: %d\n      DSP: %d\n      M9K: %d\n      M144K: %d\n   io: %d\n\n",
                numClb, numLut, numFf, numHardBlock, numPLL, numDSP, numM9K, numM144K, numIo);
        this.logger.print("   Dense: " + this.circuit.dense() + "\n");
        this.logger.print("   Num pins: " + numPins + "\n\n");
    }


    private void timePlacement(int placerIndex) {
        long seed = this.randomSeed;
        Random random = new Random(seed);

        Placer placer = this.options.getPlacer(placerIndex, this.circuit, random, this.visualizer);
        String placerName = placer.getName();

        this.startTimer(placerName);
        placer.initializeData();
        try {
            placer.place();
        } catch(PlacementException error) {
            this.logger.raise(error);
        }
        this.stopTimer();

        placer.printRuntimeBreakdown();

        this.printStatistics(placerName, true);
    }


    private void startTimer(String name) {
        this.mostRecentTimerName = name;

        Timer timer = new Timer();
        this.timers.put(name, timer);
        timer.start();
    }

    private void stopTimer() {
        this.stopTimer(this.mostRecentTimerName);
    }
    private void stopTimer(String name) {
        Timer timer = this.timers.get(name);

        if(timer == null) {
            this.logger.raise("Timer hasn't been initialized: " + name);
        } else {
            try {
                timer.stop();
            } catch(IllegalStateException error) {
                this.logger.raise("There was a problem with timer \"" + name + "\":", error);
            }
        }
    }

    private double getTime(String name) {
        Timer timer = this.timers.get(name);

        if(timer == null) {
            this.logger.raise("Timer hasn't been initialized: " + name);
            return -1;

        } else {
            double time = 0;
            try {
                time = timer.getTime();

            } catch(IllegalStateException error) {
                this.logger.raise("There was a problem with timer \"" + name + "\":", error);
            }

            return time;
        }
    }


    private void printStatistics(String prefix, boolean printTime) {

        this.logger.println(prefix + " results:");
        String format = "%-11s | %g%s\n";

        if(printTime) {
            double placeTime = this.getTime(prefix);
            this.logger.printf(format, "runtime", placeTime, " s");
        }

        // Calculate BB cost
        EfficientBoundingBoxNetCC effcc = new EfficientBoundingBoxNetCC(this.circuit);
        double totalWLCost = effcc.calculateTotalCost();
        
        
        String costFile = this.outputPlaceFile.getPath().replace(".place", ".cost");
        PrintWriter writer = null;
        try {
			writer = new PrintWriter(new BufferedWriter(new FileWriter(costFile)));
	        for(GlobalBlock block:this.circuit.getGlobalBlocks()){
	        	String output = block.getName() + "\t" + block.getIndex() + "\t" + block.getCategory() + "\t" + Math.round(effcc.calculateBlockCost(block)*1000.0)/1000.0 + "\t" + block.getColumn() + "\t" + block.getRow() + "\n";
	        	writer.write(output.replace(".", ","));
	        }
	        writer.close();
		} catch (IOException e) {
			e.printStackTrace();
		}

        
        this.logger.printf(format, "BB cost", totalWLCost, "");

        // Calculate timing cost
        this.circuit.recalculateTimingGraph();
        double totalTimingCost = this.circuit.calculateTimingCost();
        double maxDelay = this.circuit.getMaxDelay();

        this.logger.printf(format, "timing cost", totalTimingCost, "");
        this.logger.printf(format, "max delay", maxDelay, " ns");

        this.logger.println();
    }


    private void stopAndPrintTimer() {
        this.stopAndPrintTimer(this.mostRecentTimerName);
    }
    private void stopAndPrintTimer(String timerName) {
        this.stopTimer(timerName);
        this.printTimer(timerName);
    }

    private void printTimer(String timerName) {
        double placeTime = this.getTime(timerName);
        this.logger.printf("%s: %f s\n", timerName, placeTime);
    }

    private void printGCStats() {
        long totalGarbageCollections = 0;
        long garbageCollectionTime = 0;

        for(GarbageCollectorMXBean gc :
                ManagementFactory.getGarbageCollectorMXBeans()) {

            long count = gc.getCollectionCount();

            if(count >= 0) {
                totalGarbageCollections += count;
            }

            long time = gc.getCollectionTime();

            if(time >= 0) {
                garbageCollectionTime += time;
            }
        }

        this.logger.printf("Total garbage collections: %d\n", totalGarbageCollections);
        this.logger.printf("Total garbage collection time: %f s\n", garbageCollectionTime / 1000.0);
    }
}
