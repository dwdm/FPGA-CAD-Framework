package flexible_architecture.site;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Random;
import java.util.Set;

import util.Logger;

import flexible_architecture.architecture.BlockType;
import flexible_architecture.block.GlobalBlock;

public class IOSite extends AbstractSite {
	
	private int capacity;
	private Set<GlobalBlock> blocks;
	
	public IOSite(int x, int y, BlockType blockType, int capacity) {
		super(x, y, blockType);
		this.capacity = capacity;
		this.blocks = new HashSet<GlobalBlock>(capacity);
	}
	
	
	
	public GlobalBlock getRandomBlock(Random random) {
		int index = random.nextInt(this.blocks.size());
		
		Iterator<GlobalBlock> iter = this.blocks.iterator();
		for(int i = 0; i < index; i++) {
		    iter.next();
		}
		
		return iter.next();		
	}
	
	public void addBlock(GlobalBlock block) {
		if(this.blocks.size() == this.capacity) {
			Logger.raise("Tried to add a block to a full IO site");
		} else {
			this.blocks.add(block);
		}
	}
	
	public void removeBlock(GlobalBlock block) {
		boolean success = this.blocks.remove(block);
		if(!success) {
			Logger.raise("Trying to remove a block that is not present in site");
		}
	}
}
