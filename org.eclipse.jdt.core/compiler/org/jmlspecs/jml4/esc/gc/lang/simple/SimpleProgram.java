package org.jmlspecs.jml4.esc.gc.lang.simple;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.jmlspecs.jml4.esc.gc.PassifyVisitor;
import org.jmlspecs.jml4.esc.gc.lang.GcProgram;
import org.jmlspecs.jml4.esc.util.Utils;

public class SimpleProgram {
	private static final SimpleBlock[] EMPTY_BLOCK_ARRAY = SimpleBlock.EMPTY;
	public final SimpleBlock[] blocks;
	public final String startName;
	public final Map/*<String, SimpleBlock>*/ map;
	public final String methodIndicator;
	private /*@nullable*/ SimpleBlock[] sortedParentsFirst;

	public SimpleProgram(SimpleBlock[] blocks, String startName, String methodIndicator) {
		assertDistinceBlockIds(blocks);
		this.blocks = blocks;
		this.startName = startName;
		this.map = getMap(blocks);
		this.methodIndicator = methodIndicator;
	}

	private static void assertDistinceBlockIds(SimpleBlock[] blocks) {
		for (int i = 0; i < blocks.length; i++) {
			for (int j = i+1; j < blocks.length; j++) {
				Utils.assertTrue(! blocks[i].blockId.equals(blocks[j].blockId),
					"blockIds not distinct ("+i+", "+j+"): "+blocks[i].blockId); //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
			}
		}
	}

	private static Map/*<String, SimpleBlock>*/ getMap(SimpleBlock[] blocks) {
		Map/*<String, SimpleBlock>*/ result = new HashMap/*<String, SimpleBlock>*/();
		for (int i = 0; i < blocks.length; i++) {
			SimpleBlock block = blocks[i];
			result.put(block.blockId, block);
		}
		return Collections.unmodifiableMap(result);
	}

	public SimpleBlock getBlock(String blockId) {
		SimpleBlock result = (SimpleBlock) this.map.get(blockId);
		Utils.assertNotNull(result, "result is null for "+blockId); //$NON-NLS-1$
		return result;
	}

	//@ requires no cycles in this.blocks
	//@ ensures this.sortedParentsFirst != null;
	//@ ensures (* forall index of \result: forall 0<=j<index: ! \result[j].isParentOf(\result[index])*);
	public SimpleBlock[] getSortedParentsFirst() {
		if (this.sortedParentsFirst == null) {
			SimpleBlock[] result = new SimpleBlock[this.blocks.length];
			// store all the blocks not yet placed in a set.  These are the only ones we have to consider as possible parents of candidates for placement.
			Set notPlacedSet = new HashSet();
			notPlacedSet.addAll(Arrays.asList(this.blocks));

			int numPlaced = 0;
			while (notPlacedSet.size() > 0) {
				// arrays are easier to work with in Java4...
				SimpleBlock[] notPlaced = (SimpleBlock[])notPlacedSet.toArray(SimpleBlock.EMPTY);
				SimpleBlock candidate = notPlaced[0];
				int numIterations = 0;
				newCandidate:
				while (true) {
					// if an element of notPlaced is the parent of the candidate
					// then make it the candidate and start over with the scanning
					for (int i=0; i< notPlaced.length; i++) {
						if (notPlaced[i].isParentOf(candidate)) {
							Utils.assertTrue(numIterations <= notPlacedSet.size(), "exceeded max number of iterations. must be a cycle in this.blocks"); //$NON-NLS-1$
							candidate = notPlaced[i];
							numIterations++;
							continue newCandidate;
						}
					}
					// if we made it through the scan, candidate has no unplaced parents
					break newCandidate;
				}
				// so we store it in the sorted list an remove it from notPlaced
				result[numPlaced++] = candidate;
				notPlacedSet.remove(candidate);
			}
			this.sortedParentsFirst = result;
		}
		return this.sortedParentsFirst;
	}

	public String toString() {
		StringBuffer result = new StringBuffer();
		for (int i = 0; i < this.blocks.length; i++) {
			if (i != 0)
				result.append("\n"); //$NON-NLS-1$
			result.append(this.blocks[i]);
		}
		return result.toString();
	}

	public GcProgram accept(PassifyVisitor visitor) {
		return visitor.visit(this);
	}

	//@ (* forall block in this.blocks: block.getParents() != null *);
	public void findParentsOfBlocks() {
		Map/*<SimpleBlock, List<SimpleBlock>>*/ localMap = new HashMap/*<SimpleBlock, List<SimpleBlock>>*/();
		for (int i = 0; i < this.blocks.length; i++) {
			SimpleBlock parent = this.blocks[i];
			for (int j = 0; j < parent.gotos.length; j++) {
				SimpleBlock child = this.getBlock(parent.gotos[j]);
				List/*<SimpleBlock>*/ parents = (List/*<SimpleBlock>*/)localMap.get(child);
				if (parents == null) {
					parents = new ArrayList/*<SimpleBlock>*/();
					parents.add(parent);
					localMap.put(child, parents);
				} else {
					parents.add(parent);
				}
			}
		}
		for (Iterator iterator = localMap.keySet().iterator(); iterator.hasNext();) {
			SimpleBlock block = (SimpleBlock) iterator.next();
			List/*<SimpleBlock>*/ parents = (List/*<SimpleBlock>*/)localMap.get(block);
			Utils.assertTrue(parents != null || block == this.getBlock(this.startName), "only start should be an orphan"); //$NON-NLS-1$
			SimpleBlock[] aParents = (parents == null
					? EMPTY_BLOCK_ARRAY
					: (SimpleBlock[])parents.toArray(EMPTY_BLOCK_ARRAY));
			block.setParents(aParents);
		}
		this.getBlock(this.startName).setParents(EMPTY_BLOCK_ARRAY);
		// the following loop ensures the postcondition
		for (int i = 0; i < this.blocks.length; i++) {
			this.blocks[i].getParents();
		}
	}
}
