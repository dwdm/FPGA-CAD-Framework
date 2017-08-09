package place.placers.analytical;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import place.circuit.Circuit;
import place.circuit.architecture.BlockCategory;
import place.circuit.architecture.BlockType;
import place.circuit.block.GlobalBlock;
import place.placers.analytical.LiquidPlacer.CritConn;
import place.placers.analytical.LiquidPlacer.NetBlock;
import place.util.TimingTree;
import place.visual.PlacementVisualizer;

public class HardblockConnectionLegalizer extends Legalizer{
	private final double[] coorX, coorY;

    private final Block[] blocks;
    private final Net[] nets;
    private final List<Crit> crits;

    private final HardblockColumnSwap columnSwap;
    private final HardblockAnneal hardblockAnneal;
    
    private final Map<BlockType, Block[]> blocksPerBlocktype;
    private final Map<BlockType, Net[]> netsPerBlocktype;
    
    private final TimingTree timingTree;

	HardblockConnectionLegalizer(
			Circuit circuit,
            List<BlockType> blockTypes,
            List<Integer> blockTypeIndexStarts,
            double[] coorX,
            double[] coorY,
            int[] heights,
            PlacementVisualizer visualizer,
            List<LiquidPlacer.Net> nets,
            Map<GlobalBlock, NetBlock> netBlocks) {
		
		super(circuit, blockTypes, blockTypeIndexStarts, coorX, coorY, heights, nets, visualizer, netBlocks);

		this.timingTree = new TimingTree(false);

		this.timingTree.start("Initialize Hardblock Connection Legalizer Data");

		this.coorX = coorX;
		this.coorY = coorY;

		//Count the number of nets
		int maxFanout = 100;
		System.out.println("Nets with fanout larger than " + maxFanout + " are left out:");
		int numNets = 0;
		Map<Integer,Integer> fanoutMap = new HashMap<>();
		for(int i = 0; i < nets.size(); i++){
			int fanout = nets.get(i).blocks.length;
			if(fanout > maxFanout){
				if(!fanoutMap.containsKey(fanout)) fanoutMap.put(fanout, 0);
				fanoutMap.put(fanout, fanoutMap.get(fanout) + 1);
			}else{
				numNets += 1;
			}
		}
		boolean notEmpty = true;
		int min = maxFanout;
		int max = maxFanout * 2;
		while(notEmpty){
			notEmpty = false;
			int counter = 0;
			for(Integer key:fanoutMap.keySet()){
				if(key >= min && key < max){
					counter += fanoutMap.get(key);
				}else if(key >= max){
					notEmpty = true;
				}
			}
			System.out.println("\t" + counter + " nets with fanout between " + min + " and " + max);
			min = max;
			max *= 2;
		}
		System.out.println();

		//Make all objects
		this.blocks = new Block[this.coorX.length];
		this.nets = new Net[numNets];

		int l = 0;
		for(int i = 0; i < nets.size(); i++){
			int fanout = nets.get(i).blocks.length;
			if(fanout > maxFanout){
				//Do Nothing
			}else{
				double netWeight = LiquidPlacer.getWeight(fanout);
				this.nets[l] = new Net(l, netWeight);
				l++;
			}
		}
		for(int i = 0; i < this.coorX.length; i++){
			float offset = (1 - heights[i]) / 2f;
			this.blocks[i] = new Block(i, offset);
		}

		//Connect objects
		l = 0;
		for(int i = 0; i < nets.size(); i++){
			int fanout = nets.get(i).blocks.length;
			if(fanout > maxFanout){
				//Do nothing
			}else{
				Net legalizerNet = this.nets[l];
				for(NetBlock block:nets.get(i).blocks){
					Block legalizerBlock = this.blocks[block.blockIndex];

					legalizerNet.addBlock(legalizerBlock);
					legalizerBlock.addNet(legalizerNet);
				}
				l++;
			}
		}

		//Finish
		for(Net net:this.nets){
			net.finish();
		}

		this.timingTree.time("Initialize Hardblock Connection Legalizer Data");

		this.crits = new ArrayList<>();

		this.blocksPerBlocktype = new HashMap<>();
		this.netsPerBlocktype = new HashMap<>();

		this.columnSwap = new HardblockColumnSwap();
		this.hardblockAnneal = new HardblockAnneal(100);
		
		//Initialize the blocktypes
        for(int i = 0; i < blockTypes.size(); i++) {
            BlockType hardblockType = blockTypes.get(i);
            if(hardblockType.getCategory().equals(BlockCategory.HARDBLOCK) || hardblockType.getCategory().equals(BlockCategory.IO)){
            	int blocksStart = blockTypeIndexStarts.get(i);
                int blocksEnd = blockTypeIndexStarts.get(i + 1);

                if(blocksEnd > blocksStart) {
                	this.addBlocktype(hardblockType, blocksStart, blocksEnd);
                }
            }    
        }
	}
    
	//Initialization of blocks of each block type
	public void addBlocktype(BlockType blockType, int firstBlockIndex, int lastBlockIndex){
		Block[] legalizeBlocks = this.getLegalizeBlocks(firstBlockIndex, lastBlockIndex);
		Net[] legalizeNets = this.getLegalizeNets(legalizeBlocks);

		this.blocksPerBlocktype.put(blockType, legalizeBlocks);
		this.netsPerBlocktype.put(blockType, legalizeNets);
	}
	private Block[] getLegalizeBlocks(int firstBlockIndex, int lastBlockIndex){
		Block[] legalizeBlocks = new Block[lastBlockIndex - firstBlockIndex];
		for(int i = firstBlockIndex; i < lastBlockIndex; i++){
			Block legalizeBlock = this.blocks[i];
			legalizeBlocks[i - firstBlockIndex] = legalizeBlock;
			
	        //Offset test -> hard blocks have no offset
	        if(legalizeBlock.offset != 0){
	        	System.out.println("The offset of hard block is equal to " + legalizeBlock.offset + ", should be 0");
	        }
		}
		return legalizeBlocks;
	}
	private Net[] getLegalizeNets(Block[] legalizeBlocks){
		Set<Net> hardblockNets = new HashSet<Net>();
		for(Block block:legalizeBlocks){
			for(Net net:block.nets){
				hardblockNets.add(net);
			}
		}
		return hardblockNets.toArray(new Net[hardblockNets.size()]);
	}

	//UPDATE CRITICAL CONNECTIONS
	@Override
	protected void updateCriticalConnections(List<CritConn> criticalConnections){
		this.timingTree.start("Update critical connections in hardblock connection legalizer");
		
		//Clear all data
		for(Block block:this.blocks){
			block.crits.clear();
		}
		this.crits.clear();
		
		int index = 0;
		
		for(CritConn critConn:criticalConnections){
        	Block sourceBlock = this.blocks[critConn.sourceIndex];
        	Block sinkBlock = this.blocks[critConn.sinkIndex];
        	
        	Crit conn = new Crit(sourceBlock, sinkBlock, index, critConn.weight);
        	sourceBlock.addCrit(conn);
        	sinkBlock.addCrit(conn);
        	
        	this.crits.add(conn);
        	
        	index++;
		}
		
		this.timingTree.time("Update critical connections in hardblock connection legalizer");
	}
	
	//Legalize hard block
	protected void legalizeBlockType(int blocksStart, int blocksEnd) {
		if(this.blockCategory.equals(BlockCategory.HARDBLOCK)){
			this.legalizeHardblock(this.blockStart, this.blockRepeat, this.blockHeight);
		}else if(this.blockCategory.equals(BlockCategory.IO)){
			this.legalizeIO();
		}else{
    		System.out.println("unrecognized hardblock type: " + this.blockType);
    	}
	}
	
	//Legalize hard block
	public void legalizeHardblock(int firstColumn, int columnRepeat, int blockHeight){
		this.timingTree.start("Legalize " + blockType + " hardblock");
		
		int firstRow = 1;
		int rowRepeat = blockHeight;

        int numColumns = (int) Math.floor((this.width - firstColumn) / columnRepeat + 1);
        int numRows = (int) Math.floor(this.height / rowRepeat);
        
		Block[] legalizeBlocks = this.blocksPerBlocktype.get(this.blockType);
		Net[] legalizeNets = this.netsPerBlocktype.get(this.blockType);
		Column[] columns = new Column[numColumns];
		for(int c = 0; c < numColumns; c++){
			int column = firstColumn + c * columnRepeat;
			
			Site[] sites = new Site[numRows];
			for(int r = 0; r < numRows; r++){
				int row = firstRow + r * rowRepeat;
				sites[r] = new Site(column, row, this.blockType.getHeight());
			}
			columns[c] = new Column(c, column, sites);
		}
		
		//Update the coordinates off all blocks based on the current legal placement
		this.initializeLegalization(legalizeNets);

		this.timingTree.start("Find best legal coordinates for all blocks based on minimal displacement cost");
		
		//Update the coordinates of the current hard block type based on the minimal displacement from current linear placement
		for(Block block:legalizeBlocks){
			int columnIndex = (int) Math.round(Math.max(Math.min((block.x - firstColumn) / columnRepeat, numColumns - 1), 0));
			int rowIndex = (int) Math.round(Math.max(Math.min((block.y - firstRow) / rowRepeat, numRows - 1), 0));

			block.setLegal(firstColumn + columnIndex * columnRepeat, firstRow + rowIndex * rowRepeat);
			columns[columnIndex].addBlock(block);
		}

		this.timingTree.time("Find best legal coordinates for all blocks based on minimal displacement cost");

		//Column swap
		this.timingTree.start("Column swap");
		this.columnSwap.doSwap(columns);
		this.timingTree.time("Column swap");

		//Column legalize
		this.timingTree.start("Legalize columns");
		for(Column column:columns){
			column.legalize();
		}
		this.timingTree.time("Legalize columns");

		//Column anneal
		this.timingTree.start("Anneal columns");
		for(Column column:columns){
			if(column.usedPos() > 0){
				this.hardblockAnneal.doAnneal(column, this.quality);
			}
		}
		this.timingTree.time("Anneal columns");

		//Finish
		this.updateLegal(legalizeBlocks);
		this.cleanData();
		
		this.timingTree.time("Legalize " + blockType + " hardblock");
	}
	
	//Legalize IO block
	public void legalizeIO(){
		this.timingTree.start("Legalize IO");
		
		int siteCapacity = 2;
		
		Block[] legalizeBlocks = this.blocksPerBlocktype.get(this.blockType);
		Net[] legalizeNets = this.netsPerBlocktype.get(this.blockType);
		Site[] legalizeSites = new Site[2 * (this.width + this.height) * siteCapacity];
		int l = 0;
		for(int i = 1; i <= this.width; i++){
			for(int p = 0; p < siteCapacity; p++){
				legalizeSites[l++] = new Site(i, 0, this.blockType.getHeight());
				legalizeSites[l++] = new Site(i, this.height + 1, this.blockType.getHeight());
			}
		}
		for(int i = 1; i <= this.height; i++){
			for(int p = 0; p < siteCapacity; p++){
				legalizeSites[l++] = new Site(0, i, this.blockType.getHeight());
				legalizeSites[l++] = new Site(this.width + 1, i, this.blockType.getHeight());
			}
		}
		
		//Update the coordinates of the current hard block type based on the current linear placement
		this.initializeLegalization(legalizeNets);
		
		this.timingTree.start("Find best site for all IO blocks based on minimal displacement cost");
		
		//Update the coordinates of the io blocks based on the minimal displacement from current linear placement
		for(Block block:legalizeBlocks){
			
			double minimumCost = Double.MAX_VALUE;
			Site bestFreeSite = null;
			
			for(Site site:legalizeSites){
				if(!site.hasBlock()){
					double cost = (site.column - block.x) * (site.column - block.x) + (site.row - block.y) * (site.row - block.y);
					if(cost < minimumCost){
						minimumCost = cost;
						bestFreeSite = site;
					}
				}
			}
			block.setSite(bestFreeSite);
			bestFreeSite.setBlock(block);
			
			block.setLegal(bestFreeSite.column, bestFreeSite.row);
		}
		this.timingTree.time("Find best site for all IO blocks based on minimal displacement cost");

		//Anneal the IOs to find a good placement
		this.hardblockAnneal.doAnneal(legalizeBlocks, legalizeSites, this.quality);
		
		this.updateLegal(legalizeBlocks);
		this.cleanData();
		
		this.timingTree.time("Legalize IO");
	}
	private void initializeLegalization(Net[] legalizeNets){
		this.timingTree.start("Update block coordinates");
		
        for(Block block:this.blocks){
        	block.x = this.coorX[block.index];
        	block.y = this.coorY[block.index];
        }
        for(Net net:legalizeNets){
        	net.initializeConnectionCost();
        }
        for(Crit crit:this.crits){
        	crit.initializeTimingCost();
        }
        
        this.timingTree.time("Update block coordinates");
	}
    private void updateLegal(Block[] legalizeBlocks){
    	this.timingTree.start("Update legal");
    	
    	for(Block block:legalizeBlocks){
    		this.coorX[block.index] = block.x;
    		this.coorY[block.index] = block.y;
    	}
    	
    	this.timingTree.time("Update legal");
    }
    private void cleanData(){
    	this.timingTree.start("Clean data");
    	
    	for(Block block:this.blocks){
    		block.site = null;
    	}
    	
    	this.timingTree.time("Clean data");
    }
	
    /////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////// BLOCK ////////////////////////////////////
    /////////////////////////////////////////////////////////////////////////////////
	class Block{
		final int index;
		final float offset;

		double x, y;
		double oldX, oldY;
		boolean alreadySaved;

		final List<Net> nets;
		final List<Crit> crits;

		double criticality;
		
		Site site;
		Column column;
		
		Site optimalSite;

		Block(int index, float offset){
			this.index = index;
			this.offset = offset;
			
			this.alreadySaved = false;

			this.nets = new ArrayList<Net>();
			this.crits = new ArrayList<Crit>();

			this.site = null;
			this.column = null;
		}
		void addNet(Net net){
			if(!this.nets.contains(net)){
				this.nets.add(net);
			}
		}
		void addCrit(Crit crit){
			if(!this.crits.contains(crit)){
				this.crits.add(crit);
			}
		}
		
		//Criticality
		void updateCriticality(){
			this.criticality = 0.0;
			for(Net net:this.nets) this.criticality += net.weight;
			for(Crit crit:this.crits) this.criticality += crit.weight;
		}

		//// Cost ////
		double cost(){
			double cost = 0.0;
			for(Net net:this.nets) cost += net.connectionCost();
			for(Crit crit:this.crits) cost += crit.timingCost();
			return cost;
		}
		double horizontalCost(){
			double cost = 0.0;
			for(Net net:this.nets) cost += net.horizontalConnectionCost();
			for(Crit crit:this.crits) cost += crit.horizontalTimingCost();
			return cost;
		}
		double verticalCost(){
			double cost = 0.0;
			for(Net net:this.nets) cost += net.verticalConnectionCost();
			for(Crit crit:this.crits) cost += crit.verticalTimingCost();
			return cost;
		}

		void setLegal(int newLegalX, int newLegalY){
			this.tryLegal(newLegalX, newLegalY);
			this.pushTrough();
		}
		void setLegalX(int newLegalX){
			this.tryLegalX(newLegalX);
			this.pushTrough();
		}
		void setLegalY(int newLegalY){
			this.tryLegalY(newLegalY);
			this.pushTrough();
		}
		
		
		void pushTrough(){
			this.alreadySaved = false;
			
			for(Net net:this.nets) net.pushTrough();
			for(Crit crit:this.crits) crit.pushTrough();
		}
		void revert(){
			if(this.alreadySaved){
				this.x = this.oldX;
				this.y = this.oldY;
				this.alreadySaved = false;
						
				for(Net net:this.nets) net.revert();
				for(Crit crit:this.crits) crit.revert();
			}
		}

		void saveState(){
			if(!this.alreadySaved){
				this.oldX = this.x;
				this.oldY = this.y;
				this.alreadySaved = true;
			}
		}
		void tryLegal(double newLegalX, double newLegalY){
			this.tryLegalX(newLegalX);
			this.tryLegalY(newLegalY);
		}
		void tryLegalX(double newX){
			this.saveState();
			
			if(this.x != newX){
				this.x = newX;
				for(Net net:this.nets) net.tryHorizontalConnectionCost(this.oldX, this.x);
				for(Crit crit:this.crits) crit.tryHorizontalTimingCost();
			}
		}
		void tryLegalY(double newY){
			this.saveState();
			
			if(this.y != newY){
				this.y = newY;
				for(Net net:this.nets) net.tryVerticalConnectionCost(this.oldY, this.y);
				for(Crit crit:this.crits) crit.tryVerticalTimingCost();
			}
		}

    	//Site
    	void setSite(Site site){
    		this.site = site;
    	}
    	boolean hasSite(){
    		return this.site != null;
    	}
    	Site getSite(){
    		return this.site;
    	}
    	
    	//Optimal site
    	void initializeOptimalSite(){
    		this.optimalSite = this.site;
    	}
    	void saveOptimalSite(){
    		this.optimalSite = this.site;
    	}
    	void setOptimalSite(){
    		this.site = this.optimalSite;
    		this.setLegal(this.site.column, this.site.row);
    		this.site.setBlock(this);
    	}
    	
	    @Override
	    public int hashCode() {
	        return 17 + 31 * this.index;
	    }
	}

    /////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////// SITE //////////////////////////////////////
    /////////////////////////////////////////////////////////////////////////////////
	class Site {
	    final int column, row, height;
	    Block block;

	    public Site(int column, int row, int height) {
	        this.column = column;
	        this.row = row;
	        this.height = height;
	        
	        this.block = null;
	    }
	    
	    public void setBlock(Block block){
		    this.block = block;
	    }
	    public boolean hasBlock(){
	    	return this.block != null;
	    }
	    public Block getBlock(){
	        return this.block;
	    }
	    public void removeBlock(){
	    	this.block = null;
	    }
	}
    /////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////// NET //////////////////////////////////////
    /////////////////////////////////////////////////////////////////////////////////
	class Net{
		final int index;
		final double weight;

		Block[] blocks;
		final List<Block> tempBlocks;

		int size;

		double minX, maxX;
		double minY, maxY;
		double oldMinX, oldMaxX;
		double oldMinY, oldMaxY;
		boolean alreadySaved;

		boolean horizontalChange, verticalChange;
		boolean horizontalDeltaCostIncluded, verticalDeltaCostIncluded;

		Net(int index, double netWeight){
			this.index = index;
			this.tempBlocks = new ArrayList<Block>();

			this.weight = netWeight;

			this.alreadySaved = false;
			this.horizontalChange = false;
			this.verticalChange = false;
			this.horizontalDeltaCostIncluded = false;
			this.verticalDeltaCostIncluded = false;

			this.size = 0;
		}
		void addBlock(Block block){
			if(!this.tempBlocks.contains(block)){
				this.tempBlocks.add(block);
				this.size++;
			}
		}
		void finish(){
			this.blocks = new Block[this.size];
			this.tempBlocks.toArray(this.blocks);
		}

		//// Connection cost ////
		void initializeConnectionCost(){
			Block initialBlock = this.blocks[0];
	        this.minX = initialBlock.x;
	        this.maxX = initialBlock.x;
	        
	        this.minY = initialBlock.y;
	        this.maxY = initialBlock.y;
	        
	        for(Block block:this.blocks){
	            if(block.x < this.minX) {
	                this.minX = block.x;
	            }else if(block.x > this.maxX){
	            	this.maxX = block.x;
	            }
	            if(block.y < this.minY) {
	                this.minY = block.y;
	            }else if(block.y > this.maxY){
	            	this.maxY = block.y;
	            }
	        }
		}
		
		double connectionCost(){
			return this.horizontalConnectionCost() + this.verticalConnectionCost();
		}
		double horizontalConnectionCost(){
			return (this.maxX - this.minX + 1) * this.weight;
		}
		double verticalConnectionCost(){
			return (this.maxY - this.minY + 1) * this.weight;
		}
		
		void revert(){
			if(this.alreadySaved){
				if(this.horizontalChange){
					this.minX = this.oldMinX;
					this.maxX = this.oldMaxX;
					this.horizontalChange = false;
				}
				if(this.verticalChange){
					this.minY = this.oldMinY;
					this.maxY = this.oldMaxY;
					this.verticalChange = false;
				}
				
				this.alreadySaved = false;
			}
		}
		void pushTrough(){
			this.alreadySaved = false;
		}
		
		void saveState(){
			if(!this.alreadySaved){
				this.oldMinX = this.minX;
				this.oldMaxX = this.maxX;
				this.oldMinY = this.minY;
				this.oldMaxY = this.maxY;
				
				this.alreadySaved = true;
			}
		}
		// Horizontal
		void tryHorizontalConnectionCost(double oldX, double newX){
			this.saveState();
			
			if(this.size == 1){
				this.minX = this.blocks[0].x;
				this.maxX = this.blocks[0].x;
			}else if(this.size == 2){
				double l1 = this.blocks[0].x;
				double l2 = this.blocks[1].x;

				if(l1 < l2){
					this.minX = l1;
					this.maxX = l2;
				}else{
					this.maxX = l1;
					this.minX = l2;
				}
			}else{
				this.updateMinX(oldX, newX);
				this.updateMaxX(oldX, newX);
			}

            if(this.minX != this.oldMinX || this.maxX != this.oldMaxX){
            	this.horizontalChange = true;
            	this.horizontalDeltaCostIncluded = false;
            }else{
            	this.horizontalChange = false;
            	this.horizontalDeltaCostIncluded = true;
            }
		}
		double deltaHorizontalConnectionCost(){
			this.horizontalDeltaCostIncluded = true;
			return (this.maxX - this.minX - this.oldMaxX + this.oldMinX) * this.weight;
		}
		void updateMinX(double oldX, double newX){
			if(newX <= this.minX){
            	this.minX = newX;
			}else if(oldX == this.minX){
            	this.minX = this.getMinX();
            }
		}
		void updateMaxX(double oldX, double newX){
			if(newX >= this.maxX){
            	this.maxX = newX;
            }else if(oldX == this.maxX){
            	this.maxX = this.getMaxX();
            }
		}
		private double getMinX(){
	        double minX = this.blocks[0].x;
	        for(Block block:this.blocks){
	            if(block.x < minX) {
	                minX = block.x;
	            }
	        }
	        return minX;
		}
		private double getMaxX(){
	        double maxX = this.blocks[0].x;
	        for(Block block:this.blocks){
	            if(block.x > maxX) {
	                maxX = block.x;
	            }
	        }
	        return maxX;
		}

		// Vertical
		void tryVerticalConnectionCost(double oldY, double newY){
			this.saveState();
			
			if(this.size == 1){
				this.minY = this.blocks[0].y;
				this.maxY = this.blocks[0].y;
			}else if(this.size == 2){
				double l1 = this.blocks[0].y;
				double l2 = this.blocks[1].y;

				if(l1 < l2){
					this.minY = l1;
					this.maxY = l2;
				}else{
					this.maxY = l1;
					this.minY = l2;
				}
			}else{
				this.updateMinY(oldY, newY);
				this.updateMaxY(oldY, newY);
			}

            if(this.minY != this.oldMinY || this.maxY != this.oldMaxY){
            	this.verticalChange = true;
            	this.verticalDeltaCostIncluded = false;
            }else{
            	this.verticalChange = false;
            	this.verticalDeltaCostIncluded = true;
            }
        }
		double deltaVerticalConnectionCost(){
			this.verticalDeltaCostIncluded = true;
			return (this.maxY - this.minY - this.oldMaxY + this.oldMinY) * this.weight;
		}
		void updateMinY(double oldY, double newY){
			if(newY <= this.minY){
            	this.minY = newY;
			}else if(oldY == this.minY){
				this.minY = this.getMinY();
            }
		}
		void updateMaxY(double oldY, double newY){
			if(newY >= this.maxY){
            	this.maxY = newY;
            }else if(oldY == this.maxY){
            	this.maxY = this.getMaxY();
            }
		}
		private double getMinY(){
	        double minY = this.blocks[0].y;
	        for(Block block:this.blocks){
	            if(block.y < minY) {
	                minY = block.y;
	            }
	        }
	        return minY;
		}
		private double getMaxY(){
	        double maxY = this.blocks[0].y;
	        for(Block block:this.blocks){
	            if(block.y > maxY) {
	                maxY = block.y;
	            }
	        }
	        return maxY;
		}
		
	    @Override
	    public int hashCode() {
	    	return 17 + 31 * this.index;
	    }
	}

    /////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////// CRITICAL CONNECTION //////////////////////////////
    /////////////////////////////////////////////////////////////////////////////////
	class Crit {
		Block sourceBlock, sinkBlock;
		double weight;
		
		int index;

		double minX, maxX;
		double minY, maxY;
		double oldMinX, oldMaxX;
		double oldMinY, oldMaxY;
		boolean alreadySaved;
		
		boolean horizontalChange, verticalChange;
		boolean horizontalDeltaCostIncluded, verticalDeltaCostIncluded;

		Crit(Block sourceBlock, Block sinkBlock, int index, double weight){
			this.sourceBlock = sourceBlock;
			this.sinkBlock = sinkBlock;
			this.weight = weight;
			
			this.alreadySaved = false;
			this.horizontalChange = false;
			this.verticalChange = false;
			
			this.index = index;
		}

		void initializeTimingCost(){
			if(this.sourceBlock.x < this.sinkBlock.x){
				this.minX = this.sourceBlock.x;
				this.maxX = this.sinkBlock.x;
			}else{
				this.minX = this.sinkBlock.x;
				this.maxX = this.sourceBlock.x;
			}
			
			if(this.sourceBlock.y < this.sinkBlock.y){
				this.minY = this.sourceBlock.y;
				this.maxY = this.sinkBlock.y;
			}else{
				this.minY = this.sinkBlock.y;
				this.maxY = this.sourceBlock.y;
			}
		}

		void pushTrough(){
			this.alreadySaved = false;
		}
		void revert(){
			if(this.alreadySaved){
				if(this.horizontalChange){
					this.minX = this.oldMinX;
					this.maxX = this.oldMaxX;
					this.horizontalChange = false;
				}
				if(this.verticalChange){
					this.minY = this.oldMinY;
					this.maxY = this.oldMaxY;
					this.verticalChange = false;
				}

				this.alreadySaved = false;
			}
		}


		double timingCost(){
			return this.horizontalTimingCost() + this.verticalTimingCost();
		}
		double horizontalTimingCost(){
			return (this.maxX - this.minX) * this.weight;
		}
		double verticalTimingCost(){
			return (this.maxY - this.minY) * this.weight;
		}

		void saveState(){
			if(!this.alreadySaved){
				this.oldMinX = this.minX;
				this.oldMaxX = this.maxX;
				this.oldMinY = this.minY;
				this.oldMaxY = this.maxY;

				this.alreadySaved = true;
			}
		}

		void tryHorizontalTimingCost(){
			this.saveState();

			if(this.sourceBlock.x < this.sinkBlock.x){
				this.minX = this.sourceBlock.x;
				this.maxX = this.sinkBlock.x;
			}else{
				this.minX = this.sinkBlock.x;
				this.maxX = this.sourceBlock.x;
			}

			if(this.minX != this.oldMinX || this.maxX != this.oldMaxX){
				this.horizontalChange = true;
				this.horizontalDeltaCostIncluded = false;
			}else{
				this.horizontalChange = false;
				this.horizontalDeltaCostIncluded = true;
			}
        }
		double deltaHorizontalTimingCost(){
			this.horizontalDeltaCostIncluded = true;
			return (this.maxX - this.minX - this.oldMaxX + this.oldMinX) * this.weight;
		}

		void tryVerticalTimingCost(){
			this.saveState();
			
			if(this.sourceBlock.y < this.sinkBlock.y){
				this.minY = this.sourceBlock.y;
				this.maxY = this.sinkBlock.y;
			}else{
				this.minY = this.sinkBlock.y;
				this.maxY = this.sourceBlock.y;
			}

			if(this.minY != this.oldMinY || this.maxY != this.oldMaxY){
				this.verticalChange = true;
				this.verticalDeltaCostIncluded = false;
			}else{
				this.verticalChange = false;
				this.verticalDeltaCostIncluded = true;
			}
        }
		double deltaVerticalTimingCost(){
			this.verticalDeltaCostIncluded = true;
			return (this.maxY - this.minY - this.oldMaxY + this.oldMinY) * this.weight;
		}
		
	    @Override
	    public int hashCode() {
	    	return 17 + 31 * this.index;
	    }
	}

    /////////////////////////////////////////////////////////////////////////////////
    ///////////////////////////////////// COLUMN ////////////////////////////////////
    /////////////////////////////////////////////////////////////////////////////////
	class Column {
		final int index, coordinate;
		final Set<Block> blocks;
		final Site[] sites;

	    Column(int index, int coordinate, Site[] sites){
	    	this.index = index;
	    	this.coordinate = coordinate;
	    	this.blocks = new HashSet<Block>();
	    	this.sites = sites;
	    }

		void addBlock(Block block){
			this.blocks.add(block);
		}
		void removeBlock(Block block){
			this.blocks.remove(block);
		}

		int numPos(){
			return this.sites.length;
		}
		int usedPos(){
			return this.blocks.size();
		}
		void legalize(){
			for(Block block:this.blocks){
				block.updateCriticality();
			}

			for(int i = 0; i < this.blocks.size(); i++){
				Block largestCriticalityBlock = null;

				for(Block block:this.blocks){
					if(!block.hasSite()){
						if(largestCriticalityBlock == null){
							largestCriticalityBlock = block;
						}else if(block.criticality > largestCriticalityBlock.criticality){
							largestCriticalityBlock = block;
						}
					}
				}
				Site bestSite = this.getBestFreeSite(largestCriticalityBlock);
				largestCriticalityBlock.setSite(bestSite);
				bestSite.setBlock(largestCriticalityBlock);
				largestCriticalityBlock.setLegalY(bestSite.row);
			}
		}
		Site getBestFreeSite(Block block){
			Site bestSite = null;
			double minimumCost = Double.MAX_VALUE;

			for(Site site:this.sites){
				if(!site.hasBlock()){

					block.tryLegalY(site.row);
					double cost = block.verticalCost();
					block.revert();

					if(cost < minimumCost){
						minimumCost = cost;
						bestSite = site;
					}
				}
			}
			return bestSite;
		}

	    @Override
	    public int hashCode() {
	    	return 17 + 31 * this.index;
	    }
	}
}