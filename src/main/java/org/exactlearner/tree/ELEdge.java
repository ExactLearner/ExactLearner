package org.exactlearner.tree;
 
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLProperty;
import org.semanticweb.owlapi.model.OWLDataFactory;
import uk.ac.manchester.cs.owl.owlapi.OWLDataFactoryImpl;

public class ELEdge {
	private final OWLProperty label;
	private final String strLabel;
	private final ELNode node;
	private static final OWLDataFactory df = new OWLDataFactoryImpl();

	/**
	 * Constructs an edge given a label and an EL OWLClassExpression tree.
	 * @param label The label of this edge.
	 * @param tree The tree the edge points to (edges are directed).
	 */
	public ELEdge(OWLProperty label, ELNode tree) {
		this.label = label;
		this.node = tree;
		this.strLabel = toMan(label.toString());
	}
	
	/**
	 * @param str the label to set
	 */
    private String toMan(String str)
	{
		String modStr;
		modStr = str.substring(str.indexOf("#") + 1);
		modStr = modStr.substring(0, modStr.length() - 1);
		return modStr;
	}

    public OWLClassExpression transformToDescription() {
		OWLClassExpression child = node.transformToDescription();
		return df.getOWLObjectSomeValuesFrom(label.asOWLObjectProperty(), child);
	}
    
    /**
	 * @return The label of this edge.
	 */
	public OWLProperty getLabel() {
		return label;
	}

	/**
	 * @return The EL OWLClassExpression tree 
	 */
	public ELNode getNode() {
		return node;
	}
	
	public boolean isObjectProperty(){
		return label.isOWLObjectProperty();
	}
	
	@Override
	public String toString() {
		return "--" + label + "--> " + getNode().toDescriptionString();
	}

	public String getStrLabel() {
		return strLabel;
	}
}
