package org.xtext.example.ipl.viewgen.map;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.text.DecimalFormat;
import java.text.NumberFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Stack;

import org.xtext.example.ipl.viewgen.map.dijkstra.Dijkstra;
import org.xtext.example.ipl.viewgen.map.dijkstra.Edge;
import org.xtext.example.ipl.viewgen.map.dijkstra.Graph;
import org.xtext.example.ipl.viewgen.map.dijkstra.Vertex;

/**
 * @author iruchkin
 * Generates an aadl view from a map. 
 */


public class MapTranslatorAadl extends MapTranslatorUtil {

    public static final String VERSION_STR = "V0.4 - Oct 2017";

    private static String m_taskTypeLibName; 

    /**
     * Creates an AADL name for a motion task representing a given arc. 
     */
    public static String getMotTaskName(EnvMapArc a) { 
    	return "m_" + a.getSource() + "_to_" + a.getTarget();
    }

    /**
     * Generates a declaration for a task representing a given arc. 
     */
    public static String generateMotTaskDeclForArc(EnvMapArc a){
    	return getMotTaskName(a) + ": process Task;";
    }

    /**
     * Generates a task description for a given arc, assigning it a given ID.
     */
    public static String generateMotTaskForArc(EnvMapArc a, int id){
    	String res = ""; 
    	String appliesToArcName = " applies to " + getMotTaskName(a) + ";\n";
    	res += "Robot_Task_Types::task_id => " + id + 
    			appliesToArcName;
    	res += "Robot_Task_Types::start_loc => " + m_map.getNodeId(a.getSource()) + 
    			appliesToArcName;
    	res += "Robot_Task_Types::end_loc => " + m_map.getNodeId(a.getTarget()) + 
    			appliesToArcName;
    	res += "Robot_Task_Types::required_heading => " + findArcHeading(a).convertToInt() + 
    			appliesToArcName;
    	res += "Robot_Task_Types::resulting_heading => " + findArcHeading(a).convertToInt() + 
    			appliesToArcName;
    	res += "Robot_Task_Types::energy => " + getDeltaEnergy(ROBOT_FULL_SPEED_CONST, a.getDistance(), null) + 
    			appliesToArcName;
    	res += "Robot_Task_Types::task_type_enum => Forward" + 
    			appliesToArcName;
    	res += "Robot_Task_Types::task_type => 0" +
    			appliesToArcName; 
    	
    	return res;
    }
    
    /**
     * Creates an AADL name for a rotation task in a given node between two arcs: arrival and departure. 
     */
    public static String getRotTaskName(EnvMapNode n, EnvMapArc arr, EnvMapArc dep) { 
    	return "r_in_" + n.getLabel() + "_from_" + arr.getSource() + "_to_" + dep.getTarget();
    }
    
    public static void verifyValidRot(EnvMapNode n, EnvMapArc arr, EnvMapArc dep) {
    	if (!Objects.equals(n.getLabel(), arr.getTarget()) || 
    			!Objects.equals(n.getLabel(), dep.getSource()))
    		throw new IllegalArgumentException("Rotation invalid: node " + n.getLabel() +
    				" arrival to " + arr.getTarget() + " departure from " + dep.getSource());
    }



    public static String generateRotTaskDecl(EnvMapNode n, EnvMapArc arr, EnvMapArc dep){
    	verifyValidRot(n, arr, dep);
    	
    	return getRotTaskName(n, arr, dep) + ": process Task;";
    }

    public static String generateRotTask(EnvMapNode n, EnvMapArc arr, EnvMapArc dep, int id){
    	verifyValidRot(n, arr, dep);
    	String appliesToRotTask = " applies to " + getRotTaskName(n, arr, dep)  + ";\n";
    	NumberFormat f = new DecimalFormat ("#0");
    	
    	Heading arrHeading = findArcHeading(arr); 
    	Heading depHeading = findArcHeading(dep);
    	
    	String res = "";
    	res += "Robot_Task_Types::task_id => " + id + 
    			appliesToRotTask;
    	res += "Robot_Task_Types::start_loc => " + n.getId() + 
    			appliesToRotTask;
    	res += "Robot_Task_Types::end_loc => " + n.getId() + 
    			appliesToRotTask;
    	res += "Robot_Task_Types::required_heading => " + arrHeading.convertToInt() + 
    			appliesToRotTask;
    	res += "Robot_Task_Types::resulting_heading => " + depHeading.convertToInt() + 
    			appliesToRotTask;
    	res += "Robot_Task_Types::energy => " + f.format (BatteryPredictor.batteryConsumption(ROBOT_HALF_SPEED_CONST, 
    			true, ROBOT_LOC_MODE_MED_KINECT, ROBOT_LOC_MODE_HI_CPU_VAL, getRotationTime(Heading.convertToRadians(arrHeading),dep))) + 
    			appliesToRotTask;
    	res += "Robot_Task_Types::task_type_enum => Rotate" + 
    			appliesToRotTask;
    	res += "Robot_Task_Types::task_type => 1" +
    			appliesToRotTask; 
    	
    	return res;
    } 
  
    /**
     * Creates an AADL name for a empty motion task in a given node. 
     */
    public static String getEmptyTaskNameForNode(EnvMapNode n) { 
    	return "e_" + n.getLabel();
    }

    /**
     * Generates a declaration for an empty task in a given node. 
     */
    public static String generateEmptyTaskDeclForNode(EnvMapNode n){
    	return getEmptyTaskNameForNode(n) + ": process Task;";
    }

    /**
     * Generates a task description for a given arc, assigning it a given ID.
     */
    public static String generateEmptyTaskForNode(EnvMapNode n, int id){
    	String res = ""; 
    	String appliesToTaskName = " applies to " + getEmptyTaskNameForNode(n) + ";\n";
    	res += "Robot_Task_Types::task_id => " + id + 
    			appliesToTaskName;
    	res += "Robot_Task_Types::start_loc => " + n.getId() + 
    			appliesToTaskName;
    	res += "Robot_Task_Types::end_loc => " + n.getId() + 
    			appliesToTaskName;
//    	res += "Robot_Task_Types::required_heading => " + findArcHeading(a).convertToInt() + 
//    			appliesToTaskName;
//    	res += "Robot_Task_Types::resulting_heading => " + findArcHeading(a).convertToInt() + 
//    			appliesToTaskName;
    	res += "Robot_Task_Types::energy => 0" + 
    			appliesToTaskName;
    	res += "Robot_Task_Types::task_type_enum => Forward" + 
    			appliesToTaskName;
    	res += "Robot_Task_Types::task_type => 0" +
    			appliesToTaskName; 
    	
    	return res;
    }
    
    public static String getMapAadlTranslation(boolean includeRotations, boolean includeEmpty) { 
    	String preamble = "package tasks_view\n" +
    	"public\n" + 
    		"with Robot_Task_Types;\n\n" + 
    		"system TaskLibrary\n" + 
    		"end TaskLibrary;\n" + 
    		"process Task\n"  + 
    		"end Task;\n" +
    		"system implementation TaskLibrary.fullspeed\n\n" +
    		"subcomponents\n\n"; 
    	
    	String postamble = "end TaskLibrary.fullspeed;\n"+
    					   "end tasks_simple;\n";
    	
    	String motionTaskDecls = "-- Motion task decls\n";
		String motionTasks = "\nproperties\n\n-- Forward motion tasks\n";
		String rotTaskDecls = "";  
		String rotTasks = ""; 
		String emptyTaskDecls = ""; 
		String emptyTasks = ""; 

		if (includeRotations) {
			rotTaskDecls = "-- Rotation task decls\n";
			rotTasks = "\n-- Rotation tasks\n";
		}
		
		if (includeEmpty) {
			emptyTaskDecls = "\n-- Empty task decls\n";
			emptyTasks = "\n-- Empty tasks\n";
		}
		
		int taskIdCount = 0;
		
		synchronized (m_map) {
			// motion tasks
			for (int i = 0; i < m_map.getArcs().size(); i++) {
				EnvMapArc a = m_map.getArcs().get(i);
				if (a.isEnabled()) {
					motionTaskDecls += generateMotTaskDeclForArc(a) + '\n'; 
					motionTasks += generateMotTaskForArc(a, taskIdCount++) + '\n';
				}
			}
			
			//rotation tasks: consider in each node
			for (String nodeLabel : m_map.getNodes().keySet()) {
				EnvMapNode n = m_map.getNodes().get(nodeLabel); 
				
				if (includeRotations) {
					// pairs of arcs that are incoming and outgoing from this node, with non-empty rotation 
					// ok to be the same coming and going to the same node (a u-turn) 
					for (int i = 0; i < m_map.getArcs().size(); i++) { 
						for (int j = 0; j < m_map.getArcs().size(); j++) {
							EnvMapArc arr = m_map.getArcs().get(i);
							EnvMapArc dep = m_map.getArcs().get(j);
							if (arr.getTarget().equals(nodeLabel) && dep.getSource().equals(nodeLabel) && 
									findArcHeading(arr) != findArcHeading(dep)) { 
								rotTaskDecls += generateRotTaskDecl(n, arr, dep) + '\n';
								rotTasks += generateRotTask(n, arr, dep, taskIdCount++) + '\n';
							}
						}
					}
				}
				
				if (includeEmpty) {
					// empty tasks
					emptyTaskDecls += generateEmptyTaskDeclForNode(n) + '\n';
					emptyTasks += generateEmptyTaskForNode(n, taskIdCount++) + '\n';
				}
			}
			
		}
		return preamble + motionTaskDecls + '\n' + rotTaskDecls + '\n' + emptyTaskDecls + '\n' + 
				motionTasks + '\n' + rotTasks + '\n' + emptyTasks + '\n' + postamble;
    }

    /**
     * Class test
     * @param args
     */
    public static void main(String[] args) {
        setMap(new EnvMap (/*null,*/ null));
        //dummyMap.insertNode("newnode", "l1", "l2", 17.0, 69.0);
        //setMap(dummyMap);
        
        m_taskTypeLibName = "Tasklib";
        
        // AADL generation
        // params: include rotations, include empty tasks
        String aadlCode = getMapAadlTranslation(true, true);
        System.out.println(aadlCode); // Class test
        exportTranslation("/home/ivan/Dropbox/cmu/research/ipl/IPLExamples/IPLRobotProp/aadl/tasks_view.aadl", aadlCode);
    }
}
