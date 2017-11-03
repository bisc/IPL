package org.xtext.example.ipl.viewgen.map;

import java.text.DecimalFormat;
import java.text.NumberFormat;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * @author iruchkin Generates an aadl view from a map.
 */

public class MapTranslatorAadl extends MapTranslatorUtil {

	public static final String VERSION_STR = "V0.4 - Oct 2017";

	// parameters for generation
	private static String m_taskTypeLibName;
	private static String m_viewFullName;
	
	private static boolean m_includeRotation;
	private static boolean m_includeEmpty;
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
		return getMotTaskName(a) + ": process Task;";
	}

	/**
	 * Generates a task description for a given arc, assigning it a given ID.
	 */
	public static String generateMotTaskForArc(EnvMapArc a, int id) {
		String res = "";
		String appliesToArcName = " applies to " + getMotTaskName(a) + ";\n";
		res += m_taskTypeLibName + "::task_id => " + id + appliesToArcName;
		res += m_taskTypeLibName + "::start_loc => " + m_map.getNodeId(a.getSource()) + appliesToArcName;
		res += m_taskTypeLibName + "::end_loc => " + m_map.getNodeId(a.getTarget()) + appliesToArcName;
		if (m_includeRotation) {
			res += m_taskTypeLibName + "::start_head => " + findArcHeading(a).convertToInt() + appliesToArcName;
			res += m_taskTypeLibName + "::end_head => " + findArcHeading(a).convertToInt() + appliesToArcName;
		}
		res += m_taskTypeLibName + "::energy => " + getDeltaEnergy(m_robotSpeed, a.getDistance(), null)
				+ appliesToArcName;
		res += m_taskTypeLibName + "::task_type_enum => Forward" + appliesToArcName;
		res += m_taskTypeLibName + "::task_type => 0" + appliesToArcName;

		return res;
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

		return getRotTaskName(n, arr, dep) + ": process Task;";
	}

	public static String generateRotTask(EnvMapNode n, EnvMapArc arr, EnvMapArc dep, int id) {
		verifyValidRot(n, arr, dep);
		String appliesToRotTask = " applies to " + getRotTaskName(n, arr, dep) + ";\n";
		NumberFormat f = new DecimalFormat("#0");

		Heading arrHeading = findArcHeading(arr);
		Heading depHeading = findArcHeading(dep);

		String res = "";
		res += m_taskTypeLibName + "::task_id => " + id + appliesToRotTask;
		res += m_taskTypeLibName + "::start_loc => " + n.getId() + appliesToRotTask;
		res += m_taskTypeLibName + "::end_loc => " + n.getId() + appliesToRotTask;
		res += m_taskTypeLibName + "::start_head => " + arrHeading.convertToInt() + appliesToRotTask;
		res += m_taskTypeLibName + "::end_head => " + depHeading.convertToInt() + appliesToRotTask;
		res += m_taskTypeLibName + "::energy => "
				+ f.format(BatteryPredictor.batteryConsumption(m_robotSpeed, true, ROBOT_LOC_MODE_HI_KINECT,
						ROBOT_LOC_MODE_HI_CPU_VAL, getRotationTime(Heading.convertToRadians(arrHeading), dep)))
				+ appliesToRotTask;
		res += m_taskTypeLibName + "::task_type_enum => Rotate" + appliesToRotTask;
		res += m_taskTypeLibName + "::task_type => 1" + appliesToRotTask;

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
	public static String generateEmptyTaskDeclForNode(EnvMapNode n) {
		return getEmptyTaskNameForNode(n) + ": process Task;";
	}

	/**
	 * Generates a task description for a given arc, assigning it a given ID.
	 */
	public static String generateEmptyTaskForNode(EnvMapNode n, int id) {
		String res = "";
		String appliesToTaskName = " applies to " + getEmptyTaskNameForNode(n) + ";\n";
		res += m_taskTypeLibName + "::task_id => " + id + appliesToTaskName;
		res += m_taskTypeLibName + "::start_loc => " + n.getId() + appliesToTaskName;
		res += m_taskTypeLibName + "::end_loc => " + n.getId() + appliesToTaskName;
		// res += m_taskTypeLibName + "::start_head => " +
		// findArcHeading(a).convertToInt() +
		// appliesToTaskName;
		// res += m_taskTypeLibName + "::end_head => " +
		// findArcHeading(a).convertToInt() +
		// appliesToTaskName;
		res += m_taskTypeLibName + "::energy => 0" + appliesToTaskName;
		res += m_taskTypeLibName + "::task_type_enum => Empty" + appliesToTaskName;
		res += m_taskTypeLibName + "::task_type => 2" + appliesToTaskName;

		return res;
	}

	public static String getMapAadlTranslation() {
		String preamble = "-- Generated by MapTranslatorAadl\n" + "package " + m_viewFullName + "\n" + "public\n"
				+ "with Robot_Task_Types;\n\n" + "system TaskLibrary\n" + "end TaskLibrary;\n" + "process Task\n"
				+ "end Task;\n" + "system implementation TaskLibrary.fullspeed\n\n" + "subcomponents\n\n";

		String postamble = "end TaskLibrary.fullspeed;\n" + "end " + m_viewFullName + ";\n";

		String motionTaskDecls = "-- Motion task decls\n";
		String motionTasks = "\nproperties\n\n-- Forward motion tasks\n";
		String rotTaskDecls = "";
		String rotTasks = "";
		String emptyTaskDecls = "";
		String emptyTasks = "";

		if (m_includeRotation) {
			rotTaskDecls = "-- Rotation task decls\n";
			rotTasks = "\n-- Rotation tasks\n";
		}

		if (m_includeEmpty) {
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
								rotTaskDecls += generateRotTaskDecl(n, arr, dep) + '\n';
								rotTasks += generateRotTask(n, arr, dep, taskIdCount++) + '\n';
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
					emptyTaskDecls += generateEmptyTaskDeclForNode(n) + '\n';
					emptyTasks += generateEmptyTaskForNode(n, taskIdCount++) + '\n';
				}
			}
		}
		return preamble + motionTaskDecls + '\n' + rotTaskDecls + '\n' + emptyTaskDecls + '\n' + motionTasks + '\n'
				+ rotTasks + '\n' + emptyTasks + '\n' + postamble;
	}

	/**
	 * Class test
	 * 
	 * @param args
	 */
	public static void main(String[] args) {
		String path = "/home/ivan/Dropbox/cmu/research/ipl/IPLExamples/IPLRobotProp/aadl/";
		String viewTitle = "tasks_view";
		// generate for each map
		List<String> mapList = new ArrayList<String>();
		mapList.add("map1");
		mapList.add("map3");
		
		// fixing speed to full for now
		m_robotSpeed = ROBOT_FULL_SPEED_CONST; 

		for (String mapName : mapList) {
			// awkward historic scaling factors: map1 & map2 with 1, map3 with 5. 
			if (mapName.equals("map1")){
				BatteryPredictor.m_battery_scaling_factor = 1.0; 
			}
			
			if (mapName.equals("map3")){
				BatteryPredictor.m_battery_scaling_factor = 5.0; 
			}
			
			PropertiesConnector.DEFAULT.setProperty(PropertiesConnector.MAP_PROPKEY,
					"/home/ivan/Dropbox/cmu/research/ipl/IPLExamples/IPLRobotProp/model/prism/" + mapName + ".json");
			setMap(new EnvMap(/* null, */ null));

			// neither: no empties or rotations
			m_taskTypeLibName = "Robot_Task_Types";
			m_viewFullName = viewTitle + '_' + mapName + '_' + "simple";
			m_includeRotation = false;
			m_includeEmpty = false;
			exportTranslation(path + m_viewFullName + ".aadl", getMapAadlTranslation());

			// with empty tasks
			m_taskTypeLibName = "Robot_Task_Types";
			m_viewFullName =  viewTitle + '_' + mapName + '_' + "wempty";
			m_includeRotation = false;
			m_includeEmpty = true;
			exportTranslation(path + m_viewFullName + ".aadl", getMapAadlTranslation());
			
			// rotation + empty
			m_taskTypeLibName = "Robot_Task_Types";
			m_viewFullName =  viewTitle + '_' + mapName + '_' + "wempty_rot";
			m_includeRotation = true;
			m_includeEmpty = true;
			exportTranslation(path + m_viewFullName + ".aadl", getMapAadlTranslation());
		}

		System.out.println("Done with AADL view generation");
	}
}
