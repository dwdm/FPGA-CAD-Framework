package place.placers.analytical;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
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

class DetailedLegalizer extends Legalizer{
	private final List<Column> columns;
    private final List<LegalizerBlock> blocks;

	private TimingTree timingTree;

	DetailedLegalizer(	        
            Circuit circuit,
            List<BlockType> blockTypes,
            List<Integer> blockTypeIndexStarts,
            double[] coorX,
            double[] coorY,
            int[] heights,
            PlacementVisualizer visualizer,
            List<Net> nets,
            Map<GlobalBlock, NetBlock> netBlocks) {
		
        super(circuit, blockTypes, blockTypeIndexStarts, coorX, coorY, heights, nets, visualizer, netBlocks);
        this.timingTree = new TimingTree(false);

        this.blocks = new ArrayList<>();

        this.columns = new ArrayList<>();
        for(int columnIndex:circuit.getColumnsPerBlockType(BlockType.getBlockTypes(BlockCategory.CLB).get(0))){
        	Column column = new Column(columnIndex, circuit.getHeight());
        	this.columns.add(column);
        }
	}
	
	@Override
	protected void legalizeBlockType(int blocksStart, int blocksEnd) {
    	//Initialize all blocks
    	this.blocks.clear();
    	for(int b = blocksStart; b < blocksEnd; b++){
    		double x = this.coorX[b];
    		double y = this.coorY[b];

    		int height = this.heights[b];

    		int offset = (1- height) / 2;
    		this.blocks.add(new LegalizerBlock(b, x, y, offset, height * this.blockType.getHeight()));
    	}
    	
    	this.timingTree.start("Column legalizer");
    	
    	this.timingTree.start("Make sorted blocks");
    	
    	Collections.sort(this.blocks, Comparators.VERTICAL);
    	this.timingTree.time("Make sorted blocks");
    	
    	this.timingTree.start("Clear columns");
    	for(Column column:this.columns){
    		column.clear();
    	}
    	this.timingTree.time("Clear columns");

    	this.timingTree.start("Place blocks");
    	for(LegalizerBlock block:this.blocks){
    		
    		Column bestColumn = null;
    		double bestCost = Double.MAX_VALUE;
    		
    		for(Column column:this.columns){
    			if(column.usedSize + block.height <= column.height){
        			double cost = column.tryBlock(block);

        			if(cost < bestCost){
        				bestColumn = column;
        				bestCost = cost;
        			}
    			}
    		}
    		bestColumn.addBlock(block);
    	}
    	this.timingTree.time("Place blocks");

    	this.timingTree.start("Update legal");
    	for(LegalizerBlock block:this.blocks){
    		block.processed = false;
    	}
    	for(Column column:this.columns){
    		for(Site site:column.sites){
    			if(site.hasBlock()){
    				if(!site.block.processed){
    					site.block.x = site.x;
    					site.block.y = site.y;
            			site.block.processed = true;
    				}
    			}
    		}
    	}
    	this.timingTree.time("Update legal");
    	
    	for(LegalizerBlock block:this.blocks){
    		this.coorX[block.index] = block.x;
    		this.coorY[block.index] = block.y  - block.offset;
    	}
    	
    	this.timingTree.time("Column legalizer");
    }
    
	@Override
	protected void updateCriticalConnections(List<CritConn> criticalConnections) {
		//This legalization method makes no use of critical connections
	}
    class LegalizerBlock {
    	final int index;

    	double x;
    	double y;

    	final int offset;
    	final int height;

    	int ceilx, ceilxlow, ceilxhigh;
    	int ceily, ceilylow, ceilyhigh;
    	float sw, nw, se, ne;

    	boolean processed;

    	LegalizerBlock(int index, double x, double y, int offset, int height){
    		this.index = index;

    		this.x = x;
    		this.y = y;

    		this.offset = offset;
    		this.height = height;
    	}
    	double cost(int legalX, int legalY){
    		return (this.x - legalX) * (this.x - legalX) + (this.y - legalY) * (this.y - legalY);
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
    private class Column{
    	final int column;
    	final int height;

    	final Site[] sites;
    	
    	int usedSize;
    	
    	Site lastUsedSite, oldLastUsedSite;
    	Site firstFreeSite, oldFirstFreeSite;
    	
    	double cost, oldCost;
    	
    	Column(int column, int size){
    		this.column = column;
    		this.height = size;
    		
    		this.sites = new Site[this.height];
    		for(int i = 0; i < this.height; i++){
    			this.sites[i] = new Site(this.column, i + 1);
    		}
    		for(int i = 0; i < this.height; i++){
    			if(i > 0) this.sites[i].previous = this.sites[i - 1];
    			if(i < this.height - 1) this.sites[i].next = this.sites[i + 1];
    		}
    		
    		this.usedSize = 0;
    		this.cost = 0.0;
    	}
    	void clear(){
    		for(Site site:this.sites){
    			site.block = null;
    		}
    		this.usedSize = 0;
    		
    		this.cost = 0.0;
    	}
    	
    	private void saveState(){
    		for(Site site:this.sites){
    			site.saveState();
    		}
    		this.oldLastUsedSite = this.lastUsedSite;
    		this.oldFirstFreeSite = this.firstFreeSite;
    		
    		this.oldCost = this.cost;
    	}
    	private void restoreState(){
    		for(Site site:this.sites){
    			site.restoreState();
    		}
    		this.lastUsedSite = this.oldLastUsedSite;
    		this.firstFreeSite = this.oldFirstFreeSite;
    		
    		this.cost = this.oldCost;
    	}
    	private double tryBlock(LegalizerBlock block){
    		this.saveState();

    		double oldCost = this.cost;
    		this.addBlock(block);
    		double newCost = this.cost;

    		this.removeBlock(block);
    		this.restoreState();

    		return newCost - oldCost;
    	}
    	private void addBlock(LegalizerBlock block){
    		this.usedSize += block.height;

    		int optimalY = Math.max(Math.min((int)Math.round(block.y - 1), this.height - 1),  0);
    		
    		Site bestSite = this.sites[optimalY];
    		if(bestSite.hasBlock()){
        		Site currentSite = this.lastUsedSite;
        		for(int s = 0; s < block.height; s++){
        			if(currentSite.next == null){
        				this.move();
        			}else{
        				currentSite = currentSite.next;
        			}
        		}
        		
        		bestSite = this.lastUsedSite.next;
        		
        		this.putBlock(block, bestSite);
    		}else{
    			Site currentSite = bestSite;
        		for(int s = 0; s < block.height - 1; s++){
        			if(currentSite.next == null){
        				bestSite = bestSite.previous;
        				if(bestSite.hasBlock()){
        					this.lastUsedSite = bestSite;
        					this.move();
        				}
        			}else{
        				currentSite = currentSite.next;
        			}
        		}
        		this.putBlock(block, bestSite);
    		}
			this.minimumCostShift();
    	}
    	private void putBlock(LegalizerBlock block, Site site){
    		for(int s = 0; s < block.height; s++){
    			if(site == null){
    				System.out.println("Not enough space to put block at end of column");
    			}else{
    				site.setBlock(block);
    				this.lastUsedSite = site;
    				this.cost += site.block.cost(site.x, site.y);
        			
        			site = site.next;
    			}
    		}
    	}
    	private void removeBlock(LegalizerBlock block){
    		this.usedSize -= block.height;
    	}
    	private boolean move(){
    		this.firstFreeSite = this.lastUsedSite;
    		while(this.firstFreeSite.hasBlock()){
    			this.firstFreeSite = this.firstFreeSite.previous;
    			
    			if(this.firstFreeSite == null){
    				return false;
    			}
    		}
    		
    		Site currentSite = this.firstFreeSite;
    		while(currentSite != this.lastUsedSite){
    			
    			this.cost -= currentSite.next.block.cost(currentSite.next.x, currentSite.next.y);
    			currentSite.block = currentSite.next.block;
    			this.cost += currentSite.block.cost(currentSite.x, currentSite.y);
    			
    			currentSite = currentSite.next;
    		}
    		this.lastUsedSite.block = null;
    		this.lastUsedSite = this.lastUsedSite.previous;
    		
    		return true;
    	}
    	private void revert(){
    		this.lastUsedSite = this.lastUsedSite.next;
    		Site currentSite = this.lastUsedSite;
    		while(currentSite != this.firstFreeSite){
    			this.cost -= currentSite.previous.block.cost(currentSite.previous.x, currentSite.previous.y);
    			currentSite.block = currentSite.previous.block;
    			this.cost += currentSite.block.cost(currentSite.x, currentSite.y);
    			
    			currentSite = currentSite.previous;
    		}
    		this.firstFreeSite.block = null;
    	}
    	private void minimumCostShift(){
    		double minimumCost = this.cost;
    		while(this.move()){
    			double cost = this.cost;
    			if(cost < minimumCost){
    				minimumCost = cost;
    			}else{
    				revert();
    				return;
    			}
    		}
    	}
	}
    class Site {
    	final int x,y;
    	
    	LegalizerBlock block, oldBlock;
    	
    	Site previous;
    	Site next;
    	
    	public Site(int x, int y){
    		this.x = x;
    		this.y = y;
    		this.block = null;
    	}
    	boolean hasBlock(){
    		return this.block != null;
    	}
    	void setBlock(LegalizerBlock block){
    		this.block = block;
    	}
    	
    	void saveState(){
    		this.oldBlock = this.block;
    	}
    	void restoreState(){
    		this.block = this.oldBlock;
    	}
    }
    
    public static class Comparators {
    	public static Comparator<LegalizerBlock> VERTICAL = new Comparator<LegalizerBlock>() {
    		@Override
    		public int compare(LegalizerBlock b1, LegalizerBlock b2) {
    			return Double.compare(b1.y, b2.y);
    		}
    	};
    }
}
