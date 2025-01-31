package org.exactlearner.console;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.semanticweb.elk.owlapi.ElkReasonerFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.InferenceType;
import java.io.File;
public class classificationTime {




    private static final OWLOntologyManager myManager = OWLManager.createOWLOntologyManager();
    private final static int REPETITIONS=10;


    public static void main(String[] args) {
        Logger.getRootLogger().setLevel(Level.OFF);

        try {
            // targetOntology from parameters
            String filePath = args[0];

            // setLearnerSkills

            try {
                // load targetOntology
                File targetFile = new File(filePath);
                OWLOntology targetOntology = myManager.loadOntologyFromOntologyDocument(targetFile);


                long timeStart = System.currentTimeMillis();
                for(int i = 0; i<REPETITIONS; i++) {
                    ElkReasonerFactory reasoningFactory = new ElkReasonerFactory();
                    OWLReasoner elk = reasoningFactory.createReasoner(targetOntology);
                    elk.precomputeInferences(InferenceType.CLASS_HIERARCHY);
                    elk.dispose();
                }
                long timeEnd = System.currentTimeMillis();


                System.out.print(filePath + ", ");
                System.out.print((timeEnd - timeStart)/REPETITIONS);
                System.out.print(", ");
                System.out.print(targetOntology.getClassesInSignature().size());
                System.out.print(", ");
                System.out.print(targetOntology.getObjectPropertiesInSignature().size());
                System.out.println();

                myManager.removeOntology(targetOntology);

            } catch (Throwable e) {
                e.printStackTrace();
                System.out.println("error in runLearner call ----- " + e);
            }

        } catch (Throwable e) {
            // TODO Auto-generated catch block
            System.out.println("error  " + e);
            e.printStackTrace();
        } finally {

        }

    }


}
