package org.exactlearner.tree;

import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLProperty;
import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

import java.util.*;

public class ELNode {
	private final ELTree tree;
	private final TreeSet<OWLClass> label;
	private final List<ELEdge> edges;
	private final int level;
	private final ELNode  parent;
	private final boolean isClassNode;
	private static final OWLDataFactory df = new OWLDataFactoryImpl();


	public ELNode(ELNode node) {
		this.tree = node.tree;
		this.label = new TreeSet<>(node.label);
		this.edges = new LinkedList<>(node.edges);
		this.level = node.level;
		this.parent = node.parent;
		this.isClassNode = node.isClassNode;
	}

    public ELNode(ELTree tree) {
		this(tree, new TreeSet<>());
    }
	
	/**
	 * Constructs an EL OWLClassExpression tree given its root label.
	 * @param label Label of the root node.
	 */
    private ELNode(ELTree tree, TreeSet<OWLClass> label) {
		this.label = label;
		this.edges = new LinkedList<>();
		this.tree = tree;
		level = 1;
		parent = null;
		// this is the root node of the overall tree
		tree.setRootNode(this);
		tree.addNodeToLevel(this, getLevel());
		tree.setSize(tree.getSize() + label.size());
		
		isClassNode = true;
	}

    public ELNode(ELNode parentNode, OWLProperty parentProperty, Set<OWLClass> label) {
        this.label = new TreeSet<>();


		this.edges = new LinkedList<>();
		parent = parentNode;
		// the reference tree is the same as for the parent tree
		tree = parentNode.tree;
		// level increases by 1
		level = parentNode.getLevel() + 1;
		// we add an edge from the parent to this node
		ELEdge edge = new ELEdge(parentProperty, this);
		parent.getEdges().add(edge);
		// we need to update the set of nodes on a particular level
		tree.addNodeToLevel(this, getLevel());
		
		// add all classes in label
		for(OWLClass nc : label) {
			extendLabel(nc);
		}
		
		// 1 for the edge (labels are already taken care of by extendLabel)
		tree.setSize(tree.getSize() + 1);
		
		isClassNode = true;
	}


    public void remove(OWLClass cl) {
		getLabel().remove(cl);
	}
    
    
	public void remove(ELEdge e) {
		edges.add(e);

	}
	/**
	 * Adds an entry to the node label.
	 * @param newClass Class to add to label.
	 */
	public void extendLabel(OWLClass newClass) {
		getLabel().add(newClass);
		tree.setSize(tree.getSize() + 1);
	}
	
	/**
	 * Adds entries to the node label.
	 * @param newSetClass Classes to add to label.
	 */
	public void extendLabel(TreeSet<OWLClass> newSetClass) {
		for(OWLClass newClass :  newSetClass) {
			getLabel().add(newClass);
			tree.setSize(tree.getSize() + 1);
		}
	}

    public TreeSet<OWLClass> getLabel() {
		return label;
	}

    public String toString() {
		return toString(0);
	}
	
	private String toString(int indent) {
		StringBuilder indentString = new StringBuilder();
		for(int i=0; i<indent; i++)
			indentString.append("  ");
		
		StringBuilder str = new StringBuilder(indentString + getLabel().toString() + "\n");
		for(ELEdge edge : getEdges()) {
			str.append(indentString).append("-- ").append(edge.getLabel()).append(" -->\n");
			str.append(edge.getNode().toString(indent + 2));
		}
		return str.toString();
	}

	private boolean isClassNode() {
		return isClassNode;
	}

	public String toDescriptionString() {
		StringBuilder str = new StringBuilder();
		if(isClassNode()){
			if(getLabel().isEmpty()) {
				str = new StringBuilder();
			} else {
				Iterator<OWLClass> it = getLabel().iterator();
				while(it.hasNext()) {
					OWLClass nc = it.next();
					if(it.hasNext()) {
						str.append(toMan(nc.toString())).append(" and ");
					} else {
						str.append(toMan(nc.toString()));
					}
				}
			}
		}

        int current = 1;
		for(ELEdge edge : getEdges()) {
			if(current> 1) {
				str.append(" and ").append(toMan(edge.getLabel().toString())).append(" some (");
				str.append(toMan(edge.getNode().toDescriptionString())).append(")");
				continue;
			} 
			if(!getLabel().isEmpty()) {
				str.append(" and ").append(toMan(edge.getLabel().toString())).append(" some (");
				str.append(toMan(edge.getNode().toDescriptionString())).append(")");
			}else {
				str.append("  ").append(toMan(edge.getLabel().toString())).append(" some (");
				str.append(toMan(edge.getNode().toDescriptionString())).append(") ");
			}
			
			current++;
		}
		return str.toString();
	}

	private String toMan(String str)
	{
		String mod;
		mod = str.substring(str.indexOf("#")+1); 
		mod = mod.replaceAll(">", "");
		return mod;
	}



    //Reference: DL-Learner
	 public OWLClassExpression transformToDescription() {
			int nrOfElements = getLabel().size() + getEdges().size();
			if(nrOfElements == 0) {
				return df.getOWLThing();
			
			} else if(nrOfElements == 1) {
				if(getLabel().size()==1) {
					return getLabel().first();
				} else {
					ELEdge edge = getEdges().get(0);
					if(edge.isObjectProperty()){
						OWLClassExpression child = edge.getNode().transformToDescription();
						return df.getOWLObjectSomeValuesFrom(edge.getLabel().asOWLObjectProperty(), child);
					}  
					throw new RuntimeException("Description   not supported.");
				}
			// return an intersection of labels and edges
			} else {
				Set<OWLClassExpression> operands = new TreeSet<OWLClassExpression>(getLabel());
				
				for(ELEdge edge : getEdges()) {
					if(edge.isObjectProperty()){
						OWLClassExpression child = edge.getNode().transformToDescription();
						OWLClassExpression osr = df.getOWLObjectSomeValuesFrom(edge.getLabel().asOWLObjectProperty(), child);
						operands.add(osr);
					}  
				}
				return df.getOWLObjectIntersectionOf(operands);
			}
			 
		}

    public List<ELEdge> getEdges() {
        return edges;
    }

    private int getLevel() {
        return level;
    }
    
    public boolean isRoot() {
		return parent == null;
	}
}

