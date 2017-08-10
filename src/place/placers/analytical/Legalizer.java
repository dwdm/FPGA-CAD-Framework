package place.placers.analytical;

import java.util.List;
import java.util.Map;

import place.circuit.Circuit;
import place.circuit.architecture.BlockCategory;
import place.circuit.architecture.BlockType;
import place.circuit.block.GlobalBlock;
import place.placers.analytical.LiquidPlacer.CritConn;
import place.placers.analytical.LiquidPlacer.Net;
import place.placers.analytical.LiquidPlacer.NetBlock;
import place.visual.PlacementVisualizer;

abstract class Legalizer {

    protected Circuit circuit;
    protected int width, height;

    private List<BlockType> blockTypes;
    private List<Integer> blockTypeIndexStarts;
    private int numBlocks, numIOBlocks;

    protected double[] coorX, coorY;
    protected int[] heights;

    protected double quality;
    private double qualityMultiplier;
    private boolean hasQuality;

    // Properties of the blockType that is currently being legalized
    protected BlockType blockType;
    protected BlockCategory blockCategory;
    protected int blockStart, blockRepeat, blockHeight;
    
    //Visualizer
    private final PlacementVisualizer visualizer;
    private final Map<GlobalBlock, NetBlock> netBlocks;

    Legalizer(
            Circuit circuit,
            List<BlockType> blockTypes,
            List<Integer> blockTypeIndexStarts,
            double[] coorX,
            double[] coorY,
            int[] heights,
            List<Net> nets,
            PlacementVisualizer visualizer,
            Map<GlobalBlock, NetBlock> netBlocks) {

        // Store easy stuff
        this.circuit = circuit;
        this.width = this.circuit.getWidth();
        this.height = this.circuit.getHeight();

        // Store block types
        if(blockTypes.get(0).getCategory() != BlockCategory.IO) {
            throw new IllegalArgumentException("The first block type is not IO");
        }
        if(blockTypes.size() != blockTypeIndexStarts.size() - 1) {
            throw new IllegalArgumentException("The objects blockTypes and blockTypeIndexStarts don't have matching dimensions");
        }

        this.blockTypes = blockTypes;
        this.blockTypeIndexStarts = blockTypeIndexStarts;

        // Store linear solution (this array is updated by the linear solver
        this.coorX = coorX;
        this.coorY = coorY;
        this.heights = heights;

        // Cache the number of blocks
        this.numBlocks = coorX.length;
        this.numIOBlocks = blockTypeIndexStarts.get(1);
        
        // Information to visualize the legalisation progress
        this.netBlocks = netBlocks;
        this.visualizer = visualizer;
        
        this.quality = 0;
        this.qualityMultiplier = 0;
        this.hasQuality = false;
    }

    Legalizer(Legalizer legalizer) {
        this.circuit = legalizer.circuit;
        this.width = legalizer.width;
        this.height = legalizer.height;

        this.blockTypes = legalizer.blockTypes;
        this.blockTypeIndexStarts = legalizer.blockTypeIndexStarts;

        this.coorX = legalizer.coorX;
        this.coorY = legalizer.coorY;
        this.heights = legalizer.heights;

        this.numBlocks = legalizer.numBlocks;
        this.numIOBlocks = legalizer.numIOBlocks;
        
        this.visualizer = legalizer.visualizer;
        this.netBlocks = legalizer.netBlocks;
        
        this.quality = legalizer.quality;
        this.qualityMultiplier = legalizer.qualityMultiplier;
        this.hasQuality = legalizer.hasQuality;
    }
    
    void setQuality(double initialQuality, double finalQuality, int numIterations){
    	this.quality = initialQuality;
    	this.qualityMultiplier = Math.pow(finalQuality / initialQuality, 1.0 / (numIterations - 1));
    	this.hasQuality = true;
    }
    void increaseQuality(){
    	if(!this.hasQuality){
    		System.out.println("This legalizer has no quality metric!");
    	}
    	this.quality *= this.qualityMultiplier;
    }
    double getQuality(){
    	if(!this.hasQuality){
    		System.out.println("This legalizer has no quality metric!");
    	}
    	return this.quality;
    }

    protected abstract void legalizeBlockType(int blocksStart, int blocksEnd);

    protected abstract void updateCriticalConnections(List<CritConn> criticalConnections);

    void legalize(BlockType legalizeType) {
        for(int i = 0; i < this.blockTypes.size(); i++) {
        	if(this.blockTypes.get(i).equals(legalizeType)){
        		this.legalizeBlockType(i);
        	}
        }
    }

    private void legalizeBlockType(int i){
    	this.blockType = this.blockTypes.get(i);

        int blocksStart = this.blockTypeIndexStarts.get(i);
        int blocksEnd = this.blockTypeIndexStarts.get(i + 1);

        if(blocksEnd > blocksStart) {
            this.blockCategory = this.blockType.getCategory();

            this.blockStart = Math.max(1, this.blockType.getStart());
            this.blockHeight = this.blockType.getHeight();
            this.blockRepeat = this.blockType.getRepeat();
            if(this.blockRepeat == -1) {
                this.blockRepeat = this.width;
            }

            this.legalizeBlockType(blocksStart, blocksEnd);
        }
    }

    protected void addVisual(String name, double[] coorX, double[] coorY){
    	this.visualizer.addPlacement(name, this.netBlocks, coorX, coorY, -1);
    }
}
