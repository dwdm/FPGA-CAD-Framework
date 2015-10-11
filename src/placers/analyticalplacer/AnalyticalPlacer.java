package placers.analyticalplacer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import architecture.BlockType;
import architecture.BlockType.BlockCategory;
import architecture.circuit.Circuit;
import architecture.circuit.block.AbstractBlock;
import architecture.circuit.block.GlobalBlock;
import architecture.circuit.pin.AbstractPin;
import architecture.circuit.pin.GlobalPin;

import mathtools.CGSolver;
import mathtools.Crs;

import placers.Placer;


abstract class AnalyticalPlacer extends Placer {
	
	private int startingStage;
	private double[] maxUtilizationSequence;
	private double startingAnchorWeight, anchorWeightIncrease, stopRatioLinearLegal;
	
	protected Map<GlobalBlock, Integer> blockIndexes = new HashMap<GlobalBlock, Integer>(); // Maps a block (CLB or hardblock) to its integer index
	private List<BlockType> blockTypes = new ArrayList<BlockType>();
	private List<Integer> blockTypeIndexStarts = new ArrayList<Integer>();
	private int numBlocks;
	
	protected Crs xMatrix, yMatrix;
	protected double[] xVector, yVector;
	protected double[] linearX, linearY;
	
	protected CostCalculator costCalculator;
	protected Legalizer legalizer;
	
	
	static {
		//startingStage = 0 ==> start with initial solves (no anchors)
		//startingStage = 1 ==> start from existing placement that is incorporated in the packedCircuit passed with the constructor
		defaultOptions.put("starting_stage", "0");
		
		//initialize maxUtilizationSequence used by the legalizer
		defaultOptions.put("max_utilization_sequence", "0.9");
		
		//The first anchorWeight factor that will be used in the main solve loop
		defaultOptions.put("starting_anchor_weight", "0.3");
		
		//The amount with which the anchorWeight factor will be increased each iteration (multiplicative)
		defaultOptions.put("anchor_weight_increase", "1.5");
		
		//The ratio of linear solutions cost to legal solution cost at which we stop the algorithm
		defaultOptions.put("stop_ratio_linear_legal", "0.85");
	}
	
	public AnalyticalPlacer(Circuit circuit, Map<String, String> options) {
		super(circuit, options);
		
		// Parse options
		this.parsePrivateOptions();
		
		// Get number of blocks
		this.numBlocks = 0;
		for(BlockType blockType : this.circuit.getGlobalBlockTypes()) {
			if(blockType.getCategory() != BlockCategory.IO) {
				this.numBlocks += this.circuit.getBlocks(blockType).size();
			}
		}
		
		
		// Initialize blocks and positions
		this.linearX = new double[this.numBlocks];
		this.linearY = new double[this.numBlocks];
		
		int blockIndex = 0;
		this.blockTypeIndexStarts.add(blockIndex);
		
		for(BlockType blockType : this.circuit.getGlobalBlockTypes()) {
			if(blockType.getCategory() == BlockCategory.IO) {
				continue;
			}
			
			List<AbstractBlock> blocksOfType = this.circuit.getBlocks(blockType);
			for(AbstractBlock abstractBlock : blocksOfType) {
				GlobalBlock block = (GlobalBlock) abstractBlock;
				
				// Set the linear position to be equal to the current legal position
				this.linearX[blockIndex] = block.getX();
				this.linearY[blockIndex] = block.getY();
				
				this.blockIndexes.put(block, blockIndex);
				blockIndex++;
			}
			
			this.blockTypes.add(blockType);
			this.blockTypeIndexStarts.add(blockIndex);
		}
		
		this.costCalculator = this.createCostCalculator();
		this.legalizer = new Legalizer(
				circuit, this.costCalculator,
				this.blockIndexes, this.blockTypes, this.blockTypeIndexStarts,
				this.linearX, this.linearY);
	}
	
	private void parsePrivateOptions() {
		
		// Starting stage (0 or 1)
		this.startingStage = Integer.parseInt(this.options.get("starting_stage"));
		this.startingStage = Math.min(1, Math.max(0, this.startingStage)); //startingStage can only be 0 or 1
		
		// Max utilization sequence
		String maxUtilizationSequenceString = this.options.get("max_utilization_sequence");
		String[] maxUtilizationSequenceStrings = maxUtilizationSequenceString.split(",");
		this.maxUtilizationSequence = new double[maxUtilizationSequenceStrings.length];
		for(int i = 0; i < maxUtilizationSequenceStrings.length; i++) {
			this.maxUtilizationSequence[i] = Double.parseDouble(maxUtilizationSequenceStrings[i]);
		}
		
		// Anchor weights and stop ratio
		this.startingAnchorWeight = this.parseDoubleOption("starting_anchor_weight");
		this.anchorWeightIncrease = this.parseDoubleOption("anchor_weight_increase");
		this.stopRatioLinearLegal = this.parseDoubleOption("stop_ratio_linear_legal");
	}
	
	
	
	protected abstract CostCalculator createCostCalculator();
	protected abstract void initializePlacement();
	protected abstract void addExtraConnections(BlockType blockType, int startIndex, boolean firstSolve);
	
	
	public void place() {
		double pseudoWeightFactor;
		int iteration;
		
		// Initialize the data structures
		
		if(this.startingStage == 0) {
			
			//Initial linear solves, should normally be done 5-7 times
			int blockTypeIndex = -1;
			for(int i = 0; i < 7; i++) {
				this.solveLinear(true, blockTypeIndex, 0.0);
			}
			
			//Initial legalization
			this.legalizer.legalize(blockTypeIndex, this.maxUtilizationSequence[0]);
			
			pseudoWeightFactor = this.startingAnchorWeight;
			iteration = 1;
		
		
		} else {
			// Initial legalization
			this.legalizer.initializeArrays();
			pseudoWeightFactor = this.startingAnchorWeight;
			iteration = 0;
		}
		
		// Do the actual placing
		int blockTypeIndex = -1;
		double linearCost, legalCost;
		
		this.initializePlacement();
		
		do {
			String blockType = blockTypeIndex == -1 ? "all" : this.blockTypes.get(blockTypeIndex).getName();
			System.out.format("Iteration %d: pseudoWeightFactor = %f, blockType = %s",
					iteration, pseudoWeightFactor, blockType);
			
			// Solve linear
			this.solveLinear(false, blockTypeIndex, pseudoWeightFactor);
			
			// Legalize
			int sequenceIndex = Math.min(iteration, this.maxUtilizationSequence.length - 1);
			double maxUtilizationLegalizer = this.maxUtilizationSequence[sequenceIndex];
			
			this.legalizer.legalize(blockTypeIndex, maxUtilizationLegalizer);
			
			
			// Get the costs and print them
			linearCost = this.costCalculator.calculate(this.linearX, this.linearY);
			legalCost = this.legalizer.getBestCost();
			
			System.out.format(", linear cost = %f, legal cost = %f\n", linearCost, legalCost);
			
			
			blockTypeIndex = (blockTypeIndex + 2) % (this.blockTypes.size() + 1) - 1;
			if(blockTypeIndex < 0) {
				pseudoWeightFactor *= this.anchorWeightIncrease;
				iteration++;
			}
			
		} while(linearCost / legalCost < this.stopRatioLinearLegal);
		
		
		this.legalizer.updateCircuit();
	}
	
	
	
	/*
	 * Build and solve the linear system ==> recalculates linearX and linearY
	 * If it is the first time we solve the linear system ==> don't take pseudonets into account
	 */
	private void solveLinear(boolean firstSolve, int blockTypeIndex, double pseudoWeightFactor) {
		
		BlockType blockType = null;
		int startIndex, endIndex;
		
		// Solve all blocks
		if(blockTypeIndex == -1) {
			startIndex = 0;
			endIndex = this.numBlocks;
		
		// Solve blocks of one type
		} else {
			blockType = this.blockTypes.get(blockTypeIndex);
			startIndex = this.blockTypeIndexStarts.get(blockTypeIndex);
			endIndex = this.blockTypeIndexStarts.get(blockTypeIndex + 1);
		}
		
		int numBlocks = endIndex - startIndex;
		this.xMatrix = new Crs(numBlocks);
		this.yMatrix = new Crs(numBlocks);
		this.xVector = new double[numBlocks];
		this.yVector = new double[numBlocks];
		
		
		//Add pseudo connections
		if(!firstSolve) {
			// Process pseudonets
			int[] anchorPointsX = this.legalizer.getAnchorPointsX();
			int[] anchorPointsY = this.legalizer.getAnchorPointsY();
			
			for(int index = startIndex; index < endIndex; index++) {
				double deltaX = Math.max(Math.abs(anchorPointsX[index] - this.linearX[index]), 0.005);
				double deltaY = Math.max(Math.abs(anchorPointsY[index] - this.linearY[index]), 0.005);
				
				double pseudoWeightX = 2 * pseudoWeightFactor / deltaX;
				double pseudoWeightY = 2 * pseudoWeightFactor / deltaY;
				
				int relativeIndex = index - startIndex;
				this.xMatrix.setElement(relativeIndex, relativeIndex,
						this.xMatrix.getElement(relativeIndex, relativeIndex) + pseudoWeightX);
				this.yMatrix.setElement(relativeIndex, relativeIndex,
						this.yMatrix.getElement(relativeIndex, relativeIndex) + pseudoWeightY);
				
				this.xVector[relativeIndex] += pseudoWeightX * anchorPointsX[relativeIndex];
				this.yVector[relativeIndex] += pseudoWeightY * anchorPointsY[relativeIndex];
			}
		}
		
		
		// Build the linear systems (x and y are solved separately)
		
		// Loop through all sources of nets
		// This part is wirelength driven, but is also used for timing driven placement
		for(GlobalBlock sourceBlock : this.circuit.getGlobalBlocks()) {
			for(AbstractPin sourcePin : sourceBlock.getOutputPins()) {
				this.processNet(blockType, startIndex, (GlobalPin) sourcePin);
			}
		}
		
		
		// Add source sink connections
		// This is only for timing driven, and not in the first iteration
		this.addExtraConnections(blockType, startIndex, firstSolve);
		
		
		double epsilon = 0.0001;
		
		// Solve x problem
		CGSolver xSolver = new CGSolver(this.xMatrix, this.xVector);
		double[] xSolution = xSolver.solve(epsilon);
		
		// Solve y problem
		CGSolver ySolver = new CGSolver(this.yMatrix, this.yVector);
		double[] ySolution = ySolver.solve(epsilon);
		
		
		//Save results
		System.arraycopy(xSolution, 0, this.linearX, startIndex, numBlocks);
		System.arraycopy(ySolution, 0, this.linearY, startIndex, numBlocks);
	}
	
	
	
	private void processNet(BlockType blockType, int startIndex, GlobalPin sourcePin) {
		List<AbstractPin> pins = new ArrayList<AbstractPin>();
		// The source pin *must* be added first!
		pins.add(sourcePin);
		pins.addAll(sourcePin.getSinks());
		
		int numPins = pins.size();
		if(numPins < 2) {
			return;
		}
		
		
		ArrayList<Integer> netMovableBlockIndices = new ArrayList<Integer>();
		ArrayList<Integer> fixedXPositions = new ArrayList<Integer>();
		ArrayList<Integer> fixedYPositions = new ArrayList<Integer>();
		
		
		// Index = -1 means fixed block
		double minX = Double.MAX_VALUE, maxX = Double.MIN_VALUE;
		int minXIndex = -1, maxXIndex = -1;
		double minY = Double.MAX_VALUE, maxY = Double.MIN_VALUE;
		int minYIndex = -1, maxYIndex = -1;
		double Qn = getWeight(numPins);
		
		
		// Loop through all pins on the net and calculate the bounding box
		for(AbstractPin pin : pins) {
			GlobalBlock block = ((GlobalPin) pin).getOwner();
			
			double x, y;
			int index;
			
			if(isFixed(block, blockType)) {
				int intX, intY;
				
				if(block.getCategory() == BlockCategory.IO) {
					intX = block.getX();
					intY = block.getY();
				
				} else {
					index = this.blockIndexes.get(block);
					intX = this.legalizer.getAnchorPointsX()[index];
					intY = this.legalizer.getAnchorPointsY()[index];
				}
				
				
				fixedXPositions.add(intX);
				fixedYPositions.add(intY);
				
				x = intX;
				y = intY;
				index = -1;
			
			} else {
				index = this.blockIndexes.get(block);
				x = this.linearX[index];
				y = this.linearY[index];
				
				netMovableBlockIndices.add(index);
			}
				
			if(x > maxX) {
				maxX = x;
				maxXIndex = index;
			}
			if(x < minX) {
				minX = x;
				minXIndex = index;
			}
			
			if(y > maxY) {
				maxY = y;
				maxYIndex = index;
			}
			if(y < minY) {
				minY = y;
				minYIndex = index;
			}
		}
		
		
		
		double weightMultiplier = 2.0 / (numPins - 1) * Qn;
		
		// Add connections between the min and max blocks
		if(minXIndex != -1 || maxXIndex != -1) {
			this.addMinMaxConnections(minXIndex - startIndex, minX, maxXIndex - startIndex, maxX,
					weightMultiplier, this.xMatrix, this.xVector);
		}
		if(minYIndex != -1 || maxYIndex != -1) {
			this.addMinMaxConnections(minYIndex - startIndex, minY, maxYIndex - startIndex, maxY,
					weightMultiplier, this.yMatrix, this.yVector);
		}
		
		
		// Add connections between movable internal blocks and boundary blocks
		for(Integer movableIndex : netMovableBlockIndices) {
			double value = this.linearX[movableIndex];
			if(movableIndex != minXIndex) {
				this.addMovableConnections(movableIndex - startIndex, value, maxXIndex - startIndex, maxX,
						weightMultiplier, this.xMatrix, this.xVector);
			}
			if(movableIndex != maxXIndex) {
				this.addMovableConnections(movableIndex - startIndex, value, minXIndex - startIndex, minX,
						weightMultiplier, this.xMatrix, this.xVector);
			}
			
			value = this.linearY[movableIndex];
			if(movableIndex != minYIndex) {
				this.addMovableConnections(movableIndex - startIndex, value, maxYIndex - startIndex, maxY,
						weightMultiplier, this.yMatrix, this.yVector);
			}
			if(movableIndex != maxYIndex) {
				this.addMovableConnections(movableIndex - startIndex, value, minYIndex - startIndex, minY,
						weightMultiplier, this.yMatrix, this.yVector);
			}
		}
		
		
		// Add connections between fixed internal blocks and boundary blocks
		boolean firstXMin = true, firstXMax = true; 
		for(double fixedXPosition: fixedXPositions) {
			firstXMin = this.addFixedConnections(firstXMin, fixedXPosition,
					minXIndex - startIndex, minX, maxXIndex - startIndex, maxX,
					weightMultiplier, this.xMatrix, this.xVector);
			firstXMax = this.addFixedConnections(firstXMax, fixedXPosition,
					maxXIndex - startIndex, maxX, minXIndex - startIndex, minX,
					weightMultiplier, this.xMatrix, this.xVector);
		}
		
		boolean firstYMin = true, firstYMax = true;
		for(double fixedYPosition: fixedYPositions) {
			firstYMin = this.addFixedConnections(firstYMin, fixedYPosition,
					minYIndex - startIndex, minY, maxYIndex - startIndex, maxY,
					weightMultiplier, this.yMatrix, this.yVector);
			firstYMax = this.addFixedConnections(firstYMax, fixedYPosition,
					maxYIndex - startIndex, maxY, minYIndex - startIndex, minY,
					weightMultiplier, this.yMatrix, this.yVector);
		}
	}
	
	
	
	protected boolean isFixed(GlobalBlock block, BlockType blockType) {

		// IOs are always considered fixed
		if(block.getCategory() == BlockCategory.IO) {
			return true;
		
		// We are solving all block types => no types except input are fixed 
		} else if(blockType == null)  {
			return false;
		
		// The pin belongs to the block type that is being solved
		} else if(blockType.equals(block.getType())) {
			return false;
		
		// The pin belongs to a different block type
		} else {
			return true;
		}
	}


	private void addMinMaxConnections(
			int minIndex, double minCoordinate,
			int maxIndex, double maxCoordinate,
			double weightMultiplier, Crs matrix, double[] vector) {
		
		double delta = Math.max(maxCoordinate - minCoordinate, 0.005);
		double weight = weightMultiplier / delta;
		
		// Only min block is movable
		if(maxIndex < 0) {
			matrix.setElement(minIndex, minIndex, matrix.getElement(minIndex, minIndex) + weight);
			vector[minIndex] += weight * maxCoordinate;
			
		// Only max block is movable
		} else if(minIndex < 0) {
			matrix.setElement(maxIndex, maxIndex, matrix.getElement(maxIndex, maxIndex) + weight);
			vector[maxIndex] += weight * minCoordinate;
			
		// Both blocks are movable
		} else {
			matrix.setElement(minIndex, minIndex, matrix.getElement(minIndex, minIndex) + weight);
			matrix.setElement(minIndex, maxIndex, matrix.getElement(minIndex, maxIndex) - weight);
			matrix.setElement(maxIndex, minIndex, matrix.getElement(maxIndex, minIndex) - weight);
			matrix.setElement(maxIndex, maxIndex, matrix.getElement(maxIndex, maxIndex) + weight);
		}
	}
	
	private void addMovableConnections(
			int movableIndex, double movableCoordinate,
			int boundaryIndex, double boundaryCoordinate,
			double weightMultiplier, Crs matrix, double[] vector) {
		
		double delta = Math.max(Math.abs(movableCoordinate - boundaryCoordinate), 0.005);
		double weight = weightMultiplier / delta;
		
		// Boundary block is a fixed block
		// Connection between fixed and non fixed block
		if(boundaryIndex < 0) {
			matrix.setElement(movableIndex, movableIndex, matrix.getElement(movableIndex, movableIndex) + weight);
			vector[movableIndex] += weight * boundaryCoordinate;
		
		// Boundary block is not fixed
		// Connection between two non fixed blocks
		} else if(movableIndex != boundaryIndex) {
			matrix.setElement(boundaryIndex, boundaryIndex, matrix.getElement(boundaryIndex, boundaryIndex) + weight);
			matrix.setElement(boundaryIndex, movableIndex, matrix.getElement(boundaryIndex, movableIndex) - weight);
			matrix.setElement(movableIndex, boundaryIndex, matrix.getElement(movableIndex, boundaryIndex) - weight);
			matrix.setElement(movableIndex, movableIndex, matrix.getElement(movableIndex, movableIndex) + weight);
		}
	}
	
	
	private boolean addFixedConnections(boolean first, double fixedPosition,
			int index1, double coordinate1, int index2, double coordinate2,
			double weightMultiplier, Crs matrix, double[] vector) {
		
		if(fixedPosition != coordinate1 || index1 >= 0 || first == false) {
			if(index2 >= 0) {
				double delta = Math.max(Math.abs(fixedPosition - coordinate2), 0.005);
				double weight = weightMultiplier / delta;
				
				matrix.setElement(index2, index2, matrix.getElement(index2, index2) + weight);
				vector[index2] += weight * fixedPosition;
			}
			
			return first;
		
		} else {
			return false;
		}
	}
	
	
	static double getWeight(int size) {
		switch (size) {
			case 1:  return 1;
			case 2:  return 1;
			case 3:  return 1;
			case 4:  return 1.0828;
			case 5:  return 1.1536;
			case 6:  return 1.2206;
			case 7:  return 1.2823;
			case 8:  return 1.3385;
			case 9:  return 1.3991;
			case 10: return 1.4493;
			case 11:
			case 12:
			case 13:
			case 14:
			case 15: return (size-10) * (1.6899-1.4493) / 5 + 1.4493;				
			case 16:
			case 17:
			case 18:
			case 19:
			case 20: return (size-15) * (1.8924-1.6899) / 5 + 1.6899;
			case 21:
			case 22:
			case 23:
			case 24:
			case 25: return (size-20) * (2.0743-1.8924) / 5 + 1.8924;		
			case 26:
			case 27:
			case 28:
			case 29:
			case 30: return (size-25) * (2.2334-2.0743) / 5 + 2.0743;		
			case 31:
			case 32:
			case 33:
			case 34:
			case 35: return (size-30) * (2.3895-2.2334) / 5 + 2.2334;		
			case 36:
			case 37:
			case 38:
			case 39:
			case 40: return (size-35) * (2.5356-2.3895) / 5 + 2.3895;		
			case 41:
			case 42:
			case 43:
			case 44:
			case 45: return (size-40) * (2.6625-2.5356) / 5 + 2.5356;		
			case 46:
			case 47:
			case 48:
			case 49:
			case 50: return (size-45) * (2.7933-2.6625) / 5 + 2.6625;
			default: return (size-50) * 0.02616 + 2.7933;
		}
	}
}