package place.placers.analytical;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import place.circuit.Circuit;
import place.circuit.architecture.BlockCategory;
import place.circuit.architecture.BlockType;
import place.circuit.block.GlobalBlock;
import place.placers.analytical.LiquidPlacer.CritConn;
import place.placers.analytical.LiquidPlacer.Net;
import place.placers.analytical.LiquidPlacer.NetBlock;
import place.util.TimingTree;
import place.visual.PlacementVisualizer;

class GradientLegalizer extends Legalizer {

	private LegalizerBlock[] blocks;

	private final PushingSpreader spreader;
	private final double stepSize, speedAveraging;

    private final List<Integer> legalColumns;
    private final List<Integer> illegalColumns;
    private Map<Integer, Integer> columnMap;

	private TimingTree timer = null;

    GradientLegalizer(
            Circuit circuit,
            List<BlockType> blockTypes,
            List<Integer> blockTypeIndexStarts,
            double[] coorX,
            double[] coorY,
            int[] heights,
            PlacementVisualizer visualizer,
            List<Net> nets,
            Map<GlobalBlock, NetBlock> netBlocks){

        super(circuit, blockTypes, blockTypeIndexStarts, coorX, coorY, heights, nets, visualizer, netBlocks);

    	this.legalColumns = new ArrayList<>();
    	this.illegalColumns = new ArrayList<>();
    	for(BlockType blockType:circuit.getBlockTypes()){
    		if(blockType.getCategory().equals(BlockCategory.CLB)){
    			for(int column:circuit.getColumnsPerBlockType(blockType)){
    				this.legalColumns.add(column);
    			}
    		}else if(blockType.getCategory().equals(BlockCategory.HARDBLOCK)){
    			for(int column:circuit.getColumnsPerBlockType(blockType)){
    				this.illegalColumns.add(column);
    			}
    		}
    	}

    	this.columnMap = new HashMap<>();
    	int substract = 0;
    	for(int c = 1; c < circuit.getWidth() + 1; c++){
    		if(circuit.getColumnType(c).getCategory().equals(BlockCategory.HARDBLOCK)){
    			substract += 1;
    		}
    		this.columnMap.put(c - substract, substract);
    	}

    	this.stepSize = 0.6;
    	this.speedAveraging = 0.2;
    	this.spreader = new PushingSpreader(
    			this.legalColumns.size(),	//width
    			this.height,				//height
    			this.timer);

    	this.timer = new TimingTree(true);
    }

    protected void legalizeBlockType(int blocksStart, int blocksEnd) {
    	if(!this.blockType.getCategory().equals(BlockCategory.CLB)){
    		System.out.println("The GradientLegalizer can only be used for CLBs!");
    	}

        this.timer.start("Legalize BlockType");

        this.initializeData(blocksStart, blocksEnd);

        float scalingFactor = (float)this.legalColumns.size() / (this.legalColumns.size() + this.illegalColumns.size());
        for(LegalizerBlock block:this.blocks){
        	block.horizontal.coordinate = block.horizontal.coordinate * scalingFactor;
        }

        //Pushing spreader
        this.timer.start("Spreading");
        this.spreader.doSpreading(this.blocks, this.blocks.length);
        this.timer.time("Spreading");

        ////TODO ER KLOPT HIER IETS NIET?
        for(LegalizerBlock block:this.blocks){
        	int column = (int)Math.floor(block.horizontal.coordinate - 0.25);
        	
        	block.horizontal.coordinate += this.columnMap.get(column);
        }

       	this.updateLegal();

       	this.timer.time("Legalize BlockType");
    }

    //INITIALISATION
    private void initializeData(int blocksStart, int blocksEnd){
    	this.timer.start("Initialize Data");

    	//Initialize all blocks
    	this.blocks = new LegalizerBlock[blocksEnd - blocksStart];
    	for(int b = blocksStart; b < blocksEnd; b++){

    		double x = this.coorX[b];
    		double y = this.coorY[b];

    		int height = this.heights[b];

    		int offset = (1- height) / 2;
    		this.blocks[b - blocksStart] = new LegalizerBlock(b, x, y, offset, height * this.blockType.getHeight(), this.stepSize, this.speedAveraging);
    	}
    	
    	this.timer.time("Initialize Data");
    }

    //Set legal coordinates of all blocks
    private void updateLegal(){
    	this.timer.start("Update Legal");

    	for(LegalizerBlock block:this.blocks){
    		this.coorX[block.index] = block.horizontal.coordinate;
    		this.coorY[block.index] = block.vertical.coordinate - block.offset;
    	}

    	this.timer.time("Update Legal");
    }

    class LegalizerBlock {
    	final int index;
    	final int offset;
    	final int height;

    	final Dimension horizontal;
    	final Dimension vertical;

    	int ceilx;
    	int ceily;
    	float sw, nw, se, ne;

    	boolean processed;

    	LegalizerBlock(int index, double x, double y, int offset, int height, double stepSize, double speedAveraging){
    		this.index = index;

    		this.horizontal = new Dimension(x, stepSize, speedAveraging);
    		this.vertical = new Dimension(y + offset, stepSize, speedAveraging);

    		this.offset = offset;
    		this.height = height;
    	}
    	void update(){
        	this.ceilx = (int)Math.ceil(this.horizontal.coordinate + this.horizontal.coordinate);
        	this.ceily = (int)Math.ceil(this.vertical.coordinate + this.vertical.coordinate);

    		float xLeft = (this.ceilx * 0.5f) - this.horizontal.coordinate;
    		float xRight = 0.5f - xLeft;

    		float yLeft = (this.ceily * 0.5f) - this.vertical.coordinate;
    		float yRight = 0.5f - yLeft;

    		this.sw = xLeft * yLeft;
    		this.nw = xLeft * yRight;
    		this.se = xRight * yLeft;
    		this.ne = xRight * yRight;
    	}
    }
    class Dimension {
    	float coordinate;
    	float speed;
    	float force;

    	final float stepSize;
    	final float speedAveraging;

    	Dimension(double coordinate,  double stepSize, double speedAveraging){
    		this.coordinate = (float) coordinate;
    		this.speed = 0;
    		this.force = 0;

    		this.stepSize = (float) stepSize;
    		this.speedAveraging = (float) speedAveraging;
    	}

    	void setForce(float force){
    		this.force = force;
    	}

    	void solve(){
    		if(this.force != 0.0){
    			float newSpeed = this.stepSize * this.force;

            	this.speed = this.speedAveraging * this.speed + (1 - this.speedAveraging) * newSpeed;

            	this.coordinate += this.speed;
    		}
    	}
    }

	@Override
	protected void updateCriticalConnections(List<CritConn> criticalConnections) {
		//This legalization method makes no use of critical connections
	}
}
