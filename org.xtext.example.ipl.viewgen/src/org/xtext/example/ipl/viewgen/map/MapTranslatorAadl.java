package org.xtext.example.ipl.viewgen.map;

import java.text.DecimalFormat;
import java.text.NumberFormat;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

/**
 * @author iruchkin Generates an aadl view from a map.
 */

public class MapTranslatorAadl extends MapTranslatorUtil {

	public static final String VERSION_STR = "V0.4 - Oct 2017";

	// parameters for generation
	private static String m_taskPropertyLibName;
	private static String m_taskTypeLibName;
	private static String m_viewFullName;
	
	// feature switches for the generated view
	private static boolean m_includeRotation;
	private static boolean m_includeEmpty;
	private static boolean m_includeCharging;
	private static String m_robotSpeed;

	/**
	 * Creates an AADL name for a motion task representing a given arc.
	 */
	public static String getMotTaskName(EnvMapArc a) {
		return "m_" + a.getSource() + "_to_" + a.getTarget();
	}

	/**
	 * Generates a declaration for a task representing a given arc.
	 */
	public static String generateMotTaskDeclForArc(EnvMapArc a) {
		return getMotTaskName(a) + ": process " + m_taskTypeLibName + "::Task;\n";
	}

	/**
	 * Generates a task description for a given arc, assigning it a given ID.
	 */
	public static String generateMotTaskForArc(EnvMapArc a, int id) {
		String res = "";
		String appliesToArcName = " applies to " + getMotTaskName(a) + ";\n";
		res += m_taskPropertyLibName + "::task_id => " + id + appliesToArcName;
		res += m_taskPropertyLibName + "::start_loc => " + m_map.getNodeId(a.getSource()) + appliesToArcName;
		res += m_taskPropertyLibName + "::end_loc => " + m_map.getNodeId(a.getTarget()) + appliesToArcName;
		if (m_includeRotation) {
			res += m_taskPropertyLibName + "::start_head => " + findArcHeading(a).convertToInt() + appliesToArcName;
			res += m_taskPropertyLibName + "::end_head => " + findArcHeading(a).convertToInt() + appliesToArcName;
		}
		res += m_taskPropertyLibName + "::energy => " + getDeltaEnergy(m_robotSpeed, a.getDistance(), null)
				+ appliesToArcName;
		res += m_taskPropertyLibName + "::task_type_enum => Forward" + appliesToArcName;
		res += m_taskPropertyLibName + "::task_type => 0" + appliesToArcName;

		return res + '\n';
	}

	/**
	 * Creates an AADL name for a rotation task in a given node between two
	 * arcs: arrival and departure.
	 */
	public static String getRotTaskName(EnvMapNode n, EnvMapArc arr, EnvMapArc dep) {
		return "r_in_" + n.getLabel() + "_from_" + arr.getSource() + "_to_" + dep.getTarget();
	}

	public static void verifyValidRot(EnvMapNode n, EnvMapArc arr, EnvMapArc dep) {
		if (!Objects.equals(n.getLabel(), arr.getTarget()) || !Objects.equals(n.getLabel(), dep.getSource()))
			throw new IllegalArgumentException("Rotation invalid: node " + n.getLabel() + " arrival to "
					+ arr.getTarget() + " departure from " + dep.getSource());
	}

	public static String generateRotTaskDecl(EnvMapNode n, EnvMapArc arr, EnvMapArc dep) {
		verifyValidRot(n, arr, dep);

		return getRotTaskName(n, arr, dep) + ": process " + m_taskTypeLibName+ "::Task;\n";
	}

	public static String generateRotTask(EnvMapNode n, EnvMapArc arr, EnvMapArc dep, int id) {
		verifyValidRot(n, arr, dep);
		String appliesToRotTask = " applies to " + getRotTaskName(n, arr, dep) + ";\n";
		NumberFormat f = new DecimalFormat("#0");

		Heading arrHeading = findArcHeading(arr);
		Heading depHeading = findArcHeading(dep);

		String res = "";
		res += m_taskPropertyLibName + "::task_id => " + id + appliesToRotTask;
		res += m_taskPropertyLibName + "::start_loc => " + n.getId() + appliesToRotTask;
		res += m_taskPropertyLibName + "::end_loc => " + n.getId() + appliesToRotTask;
		res += m_taskPropertyLibName + "::start_head => " + arrHeading.convertToInt() + appliesToRotTask;
		res += m_taskPropertyLibName + "::end_head => " + depHeading.convertToInt() + appliesToRotTask;
		res += m_taskPropertyLibName + "::energy => "
				+ f.format(BatteryPredictor.batteryConsumption(m_robotSpeed, true, ROBOT_LOC_MODE_HI_KINECT,
						ROBOT_LOC_MODE_HI_CPU_VAL, getRotationTime(Heading.convertToRadians(arrHeading), dep)))
				+ appliesToRotTask;
		res += m_taskPropertyLibName + "::task_type_enum => Rotate" + appliesToRotTask;
		res += m_taskPropertyLibName + "::task_type => 1" + appliesToRotTask;

		return res + '\n';
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
	public static String generateEmptyTaskDeclForNode(EnvMapNode n) {
		return getEmptyTaskNameForNode(n) + ": process " + m_taskTypeLibName + "::Task;\n";
	}

	/**
	 * Generates an empty task description for a given arc, assigning it a given ID.
	 */
	public static String generateEmptyTaskForNode(EnvMapNode n, int id) {
		String res = "";
		String appliesToTaskName = " applies to " + getEmptyTaskNameForNode(n) + ";\n";
		res += m_taskPropertyLibName + "::task_id => " + id + appliesToTaskName;
		res += m_taskPropertyLibName + "::start_loc => " + n.getId() + appliesToTaskName;
		res += m_taskPropertyLibName + "::end_loc => " + n.getId() + appliesToTaskName;
//		 res += m_taskTypeLibName + "::start_head => " +
//		 findArcHeading(a).convertToInt() +
//		 appliesToTaskName;
//		 res += m_taskTypeLibName + "::end_head => " +
//		 findArcHeading(a).convertToInt() +
//		 appliesToTaskName;
		res += m_taskPropertyLibName + "::energy => 0" + appliesToTaskName;
		res += m_taskPropertyLibName + "::task_type_enum => Empty" + appliesToTaskName;
		res += m_taskPropertyLibName + "::task_type => 2" + appliesToTaskName;

		return res + '\n';
	}
	
	/**
	 * Generates a declaration for a charging task in a given node.
	 */
	public static String generateCharTaskDeclForNode(EnvMapNode n) {
		if (n.isChargingStation()) 
			return getCharTaskNameForNode(n) + ": process " + m_taskTypeLibName + "::Task;\n";
		else 
			return "";
	}

	/**
	 * Creates an AADL name for a charging task in a given node.
	 */
	public static String getCharTaskNameForNode(EnvMapNode n) {
		return "ch_" + n.getLabel();
	}

	/**
	 * Generates a charging task description for a given arc, assigning it a given ID.
	 */
	public static String generateCharTaskForNode(EnvMapNode n, int id) {
		if (!n.isChargingStation()) 
			return "";
		
		String res = "";
		String appliesToTaskName = " applies to " + getCharTaskNameForNode(n) + ";\n";
		
		res += m_taskPropertyLibName + "::task_id => " + id + appliesToTaskName;
		res += m_taskPropertyLibName + "::start_loc => " + n.getId() + appliesToTaskName;
		res += m_taskPropertyLibName + "::end_loc => " + n.getId() + appliesToTaskName;
		res += m_taskPropertyLibName + "::energy => -" + String.valueOf( 
				Math.round (BatteryPredictor.batteryCharge(ROBOT_CHARGING_TIME)))
					+ appliesToTaskName; // set the charging energy as a negative value
		res += m_taskPropertyLibName + "::task_type_enum => Charging" + appliesToTaskName;
		res += m_taskPropertyLibName + "::task_type => 3" + appliesToTaskName;
		
		return res + '\n';
	}
	
	/**
	 * Get a complete aadl translation
	 */
	public static String getMapAadlTranslation() {
		String preamble = "-- Generated by MapTranslatorAadl\n" + "package " + m_viewFullName + "\n" + "public\n"
				+ "with " + m_taskPropertyLibName + ", " +  m_taskTypeLibName + ";\n\n" + "system TaskLibrary\n" + "end TaskLibrary;\n" + "system implementation TaskLibrary.fullspeed\n\n" + "subcomponents\n\n";

		String postamble = "end TaskLibrary.fullspeed;\n" + "end " + m_viewFullName + ";\n";

		String motionTaskDecls = "-- Motion task decls\n";
		String motionTasks = "\nproperties\n\n-- Forward motion tasks\n-- Assumption:start/end locs are IDs of locations, not refs to them\n";
		String rotTaskDecls = "";
		String rotTasks = "";
		String emptyTaskDecls = "";
		String emptyTasks = "";
		String chargingTaskDecls = "";
		String chargingTasks = "";

		if (m_includeRotation) {
			rotTaskDecls = "-- Rotation task decls\n";
			rotTasks = "\n-- Rotation tasks\n";
		}

		if (m_includeEmpty) {
			emptyTaskDecls = "\n-- Empty task decls\n";
			emptyTasks = "\n-- Empty tasks\n";
		}
		
		if (m_includeCharging) {
			chargingTaskDecls = "\n-- Charging task decls\n";
			chargingTasks = "\n-- Charging tasks\n";
		}

		int taskIdCount = 0;

		synchronized (m_map) {
			// motion tasks
			for (int i = 0; i < m_map.getArcs().size(); i++) {
				EnvMapArc a = m_map.getArcs().get(i);
				if (a.isEnabled()) {
					motionTaskDecls += generateMotTaskDeclForArc(a);
					motionTasks += generateMotTaskForArc(a, taskIdCount++);
				}
			}

			// rotation tasks: consider in each node
			for (String nodeLabel : m_map.getNodes().keySet()) {
				EnvMapNode n = m_map.getNodes().get(nodeLabel);

				if (m_includeRotation) {
					// pairs of arcs that are incoming and outgoing from this
					// node, with non-empty rotation
					// ok to be the same coming and going to the same node (a
					// u-turn)
					for (int i = 0; i < m_map.getArcs().size(); i++) {
						for (int j = 0; j < m_map.getArcs().size(); j++) {
							EnvMapArc arr = m_map.getArcs().get(i);
							EnvMapArc dep = m_map.getArcs().get(j);
							if (arr.getTarget().equals(nodeLabel) && dep.getSource().equals(nodeLabel)
									&& findArcHeading(arr) != findArcHeading(dep)) {
								rotTaskDecls += generateRotTaskDecl(n, arr, dep);
								rotTasks += generateRotTask(n, arr, dep, taskIdCount++);
							}
						}
					}
				}
			}

			// empty tasks; separate loop for contiguous IDs (for convenience of
			// reading)
			for (String nodeLabel : m_map.getNodes().keySet()) {
				EnvMapNode n = m_map.getNodes().get(nodeLabel);
				if (m_includeEmpty) {
					emptyTaskDecls += generateEmptyTaskDeclForNode(n);
					emptyTasks += generateEmptyTaskForNode(n, taskIdCount++);
				}
				
				if (m_includeCharging) {
					chargingTaskDecls += generateCharTaskDeclForNode(n);
					chargingTasks += generateCharTaskForNode(n, taskIdCount++);
				}
			}
		}
		return preamble + 
				motionTaskDecls + '\n' + rotTaskDecls + '\n' + emptyTaskDecls + '\n' + chargingTaskDecls + '\n' +
				motionTasks + '\n' + rotTasks + '\n' + emptyTasks + '\n' + chargingTasks + '\n' +
				postamble;
	}

	/**
	 * Standalone run of generating AADL from map*.json.
	 * To run this test, set the following environment variables: 
	 *
	 *    MAP_DIR: where input map files are, e.g. /home/ivan/Dropbox/cmu/research/ipl/IPLExamples/IPLRobotProp/model/map
	 *    PRISM_OUT_DIR: where output prism files will go, e.g., /home/ivan/Dropbox/cmu/research/ipl/IPLExamples/IPLRobotProp/model/prism
     *    AADL_OUT_DIR: where output aadl files will go, e.g., /home/ivan/Dropbox/cmu/research/ipl/IPLExamples/IPLRobotProp/model/aadl
	 * 
	 */
	public static void main(String[] args) {
		String path = PropertiesConnector.DEFAULT.getProperty(PropertiesConnector.AADL_OUTPUT_DIR_PROPKEY)
				+ '/';
		String viewTitle = "tasks_view";
		// map names -> scaling factors
		Map<String, Double> maps2Scaling = new HashMap<String, Double>();
		maps2Scaling.put("map1", 1.0);
		maps2Scaling.put("map2", 1.0);
		maps2Scaling.put("map3b", 5.0);
		
		// fixing speed to full for now
		m_robotSpeed = ROBOT_FULL_SPEED_CONST; 

		for (String mapName : maps2Scaling.keySet()) {
			// awkward historic scaling factors: map0 & map1 & map2 with 1, map3a/b with 5. 
			// cannot generate for map0 or map3a because missing input data
			BatteryPredictor.m_battery_scaling_factor = maps2Scaling.get(mapName); 
			
			PropertiesConnector.DEFAULT.setProperty(PropertiesConnector.MAP_NAME_PROPKEY,
					mapName + ".json");
			setMap(new EnvMap(/* null, */ null));

			// neither: no empties or rotations
			m_taskPropertyLibName = "Robot_Task_Properties";
			m_taskTypeLibName = "Robot_Task_Types";
			m_viewFullName = viewTitle + '_' + mapName + '_' + "simple";
			m_includeRotation = false;
			m_includeEmpty = false;
			m_includeCharging = false;
			exportTranslation(path +  m_viewFullName + ".aadl", getMapAadlTranslation());

			// with empty tasks
			m_taskPropertyLibName = "Robot_Task_Properties";
			m_taskTypeLibName = "Robot_Task_Types";
			m_viewFullName =  viewTitle + '_' + mapName + '_' + "wempty";
			m_includeRotation = false;
			m_includeEmpty = true;
			m_includeCharging = false;
			exportTranslation(path + m_viewFullName + ".aadl", getMapAadlTranslation());
			
			// empty + charging
			m_taskPropertyLibName = "Robot_Task_Properties";
			m_taskTypeLibName = "Robot_Task_Types";
			m_viewFullName =  viewTitle + '_' + mapName + '_' + "wempty_char";
			m_includeRotation = false;
			m_includeEmpty = true;
			m_includeCharging = true;
			exportTranslation(path + m_viewFullName + ".aadl", getMapAadlTranslation());
			
			// empty + rotation
			m_taskPropertyLibName = "Robot_Task_Properties";
			m_taskTypeLibName = "Robot_Task_Types";
			m_viewFullName =  viewTitle + '_' + mapName + '_' + "wempty_rot";
			m_includeRotation = true;
			m_includeEmpty = true;
			m_includeCharging = false;
			exportTranslation(path + m_viewFullName + ".aadl", getMapAadlTranslation());
			
			// rotation + empty + charging
			m_taskPropertyLibName = "Robot_Task_Properties";
			m_taskTypeLibName = "Robot_Task_Types";
			m_viewFullName =  viewTitle + '_' + mapName + '_' + "wempty_rot_char";
			m_includeRotation = true;
			m_includeEmpty = true;
			m_includeCharging = true;
			exportTranslation(path + m_viewFullName + ".aadl", getMapAadlTranslation());
		}

		System.out.println("Done with AADL views generation, exported to " + path + "*.aadl");
	}
}
