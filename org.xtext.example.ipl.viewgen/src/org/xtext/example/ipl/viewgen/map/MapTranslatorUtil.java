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
 * Contains constants shared between Prism and AADL generation. 
 */


public class MapTranslatorUtil {

    public static final String ROBOT_BATTERY_RANGE_MIN = "0";
    public static final String ROBOT_BATTERY_RANGE_MAX = "32560";
    public static final String ROBOT_BATTERY_RANGE_MAX_CONST = "MAX_BATTERY";
    public static final String INITIAL_ROBOT_BATTERY_CONST = "INITIAL_BATTERY";
    public static final String ROBOT_BATTERY_DELTA = "10"; // Constant for the time being, this should be transition+context dependent
    public static final float ROBOT_CHARGING_TIME = 15.0f;

    public static final String ROBOT_FULL_SPEED_CONST = "FULL_SPEED"; // These are just symbolic constants for PRISM
    public static final String ROBOT_HALF_SPEED_CONST = "HALF_SPEED";
    public static final String ROBOT_DR_SPEED_CONST = "DR_SPEED";
    
    public static final float ROBOT_FULL_SPEED_VALUE = 0.68f; // m/s
    public static final float ROBOT_HALF_SPEED_VALUE = 0.35f;
    public static final float ROBOT_DR_SPEED_VALUE = 0.25f; // Dead reckoning ` value .. this is implicit in ROBOT_LOC_MODE_LO

    public static final float  ROBOT_ROTATIONAL_SPEED_VALUE = 1.5f;             // rad/s

    public static final String ROBOT_LOC_MODE_LO_CONST = "LOC_LO";
    public static final String ROBOT_LOC_MODE_LO_VAL = "0";
    public static final String ROBOT_LOC_MODE_MED_CONST = "LOC_MED";
    public static final String ROBOT_LOC_MODE_MED_VAL = "1";
    public static final String ROBOT_LOC_MODE_HI_CONST = "LOC_HI";
    public static final String ROBOT_LOC_MODE_HI_VAL = "2";
    public static final double ROBOT_LOC_MODE_LO_CPU_VAL = 20; //96.3875;
    public static final double ROBOT_LOC_MODE_MED_CPU_VAL = 95; // TODO: Change by actual value
    public static final double ROBOT_LOC_MODE_HI_CPU_VAL = 95; // TODO: Change by actual value
    public static final boolean ROBOT_LOC_MODE_HI_KINECT = true;
    public static final boolean ROBOT_LOC_MODE_MED_KINECT = true;
    public static final boolean ROBOT_LOC_MODE_LO_KINECT = false;
    public static final String ROBOT_LOC_MODE_MAX_RECONF_CONST = "LOC_MODE_RECONF_MAX";
    public static final String ROBOT_LOC_MODE_MAX_RECONF_VAL = "2";

    public static final float  MAXIMUM_KINECT_OFF_DISTANCE_VAL = 6.0f; // Maximum driving distance with kinect off in m.

    // Goal and stop condition configuration constants
    public static final double MAX_DISTANCE = 999.0; // Distance assigned to disabled edges (for distance reward computation)
    public static final double DEFAULT_TIME_TACTIC_TIME=1; // Tactics are not instantaneous;
    public static final String TACTIC_PREFIX="t";

    // Properties' indices
    public static final int TIME_PROPERTY = 0;
    public static final int ACCURACY_PROPERTY = 1;

    protected static EnvMap m_map;

    /**
     * Sets the map to translate into a PRISM specification
     * @param map an EnvMap encoding the graph that captures the physical space
     */
    public static void setMap(EnvMap map){
        m_map = map;
    }

    /**
     * Generates battery update formulas employed in updates of movement commands in robot module
     * @return String PRISM encoding for possible battery updates (corresponding to movements between map locations)
     */

    public static String getDeltaEnergy(String speed, double distance, String sensing){
        return String.valueOf (Math.round (BatteryPredictor.batteryConsumption (speed, sensing, SpeedPredictor.moveForwardTimeSimple(distance, speed))));
    }

    /**
     * Returns the rotation time in seconds from a given robot orientation to the right angle before it
     * starts moving towards a given location (target of arc a)
     * @param robotOrientation orientation of the robot (angle in Radians, from 0 to 2pi)
     * @param a Map arc 
     * @return Rotation time in seconds
     */
    public static double getRotationTime(double robotOrientation, EnvMapArc a){    	
        double theta = Math.abs(robotOrientation-findArcOrientation(a)); // subtracting [0, 2pi) from [0, 2pi)
        double min_theta = (theta > Math.PI) ? 2*Math.PI - theta : theta;
        return (min_theta/ROBOT_ROTATIONAL_SPEED_VALUE); 
    }

    /**
     * Determines the angle (in Radians) between two endpoints of an arc, taking the source node of the arc
     * as the reference of coordinates in the plane. Used to determine the part of the time reward structure 
     * associated with in-node robot rotations.
     * @param a Map arc
     * @return angle in radians between a.m_source and a.m_target, in the [0, 2pi) interval
     */
    public static double findArcOrientation(EnvMapArc a){
        synchronized (m_map) {
            double nodeX = m_map.getNodeX(a.getSource());
            double nodeY = m_map.getNodeY(a.getSource());
            double nodeX2 = m_map.getNodeX(a.getTarget());
            double nodeY2 = m_map.getNodeY(a.getTarget());
            if (nodeX == Double.NEGATIVE_INFINITY || nodeX2 == Double.NEGATIVE_INFINITY) return 0;
            return findArcOrientation( nodeX, nodeY, nodeX2, nodeY2);
        }
    }

    /**
     * Determines the angle (in Radians) of a vector (source, target), taking the source
     * as the reference of coordinates in the plane.
     * @return angle in radians, ranging from -pi to pi
     */
    public static double findArcOrientation(double src_x, double src_y, double tgt_x, double tgt_y){
    	double angle = Math.atan2( tgt_y - src_y, tgt_x - src_x); // from -pi to pi
    	
    	if (angle < 0) // convert to [0, 2pi)
    		angle += 2*Math.PI;
    	
        return angle;
    }

    /**
     * Determines the heading between two endpoints of an arc (snaps result of findArcOrientation to one of the predetermined headings)
     * @param a Map arc
     * @return heading enum arc heading
     */
    public static Heading findArcHeading (EnvMapArc a) {
        return Heading.convertFromRadians(findArcOrientation(a));
    }


    public static Stack<String> m_connectionPath = null; // Aux data structures for finding all paths between arbitrary locations
    public static List<Stack> m_connectionPaths = null;

    /**
     * Generates all non-cyclic paths between two locations in map
     * @param node1
     * @param node2
     */
    public static List<Stack> goFindAllPaths(String node1, String node2){
        m_connectionPath = new Stack<String>();
        m_connectionPath.push(node1);
        m_connectionPaths = new ArrayList<>();
        findAllPaths (node1, node2);
        for (int i=0; i<m_connectionPaths.size();i++) {
            m_connectionPaths.get(i).add(node2);
        }
        return m_connectionPaths;
    }

    public static synchronized void findAllPaths(String src, String tgt) {
        for (String nextNode : m_map.getNeighbors(src)){		  
            if (nextNode.equals(tgt)){
                Stack temp = new Stack<String>();
                for (String node1 : m_connectionPath) {
                    temp.add(node1);
                }
                m_connectionPaths.add(temp);
            } else if (!m_connectionPath.contains(nextNode)) {
                m_connectionPath.push(nextNode);
                findAllPaths(nextNode, tgt);
                m_connectionPath.pop();
            }
        }

    }

    /**
     * Returns shortest distance between two nodes computed using Dijkstra's Algorithm
     * @param node1 String label of source node (associated with an EnvMapNode in the map to translate)
     * @param node2 String label of target node (associated with an EnvMapNode in the map to translate)
     * @return float shortest distance between node1 and node2
     */
    public static double shortestPathDistance (String node1, String node2) {
        synchronized (m_map) {
            Graph graph = new Graph();
            Vertex[] vertices = new Vertex[m_map.getNodeCount()];

            Map<String, Integer> node_indexes = new HashMap<> ();

            int i=0;
            for (Map.Entry<String,EnvMapNode> entry : m_map.getNodes().entrySet() ){
                vertices[i] = new Vertex(entry.getKey());
                graph.addVertex(vertices[i], true);
                node_indexes.put (entry.getKey (), i);
                i++;
            }

            Edge[] edges = new Edge[m_map.getArcCount()];


            for (i=0;i<m_map.getArcs().size();i++){
                EnvMapArc a = m_map.getArcs().get(i);
                Vertex source = vertices[(node_indexes.get (a.getSource ()))];
                Vertex target = vertices[(node_indexes.get (a.getTarget ()))];
                if (a.isEnabled()){
                    edges[i] = new Edge(source, target, a.getDistance());
                } else {
                    edges[i] = new Edge(source, target, MAX_DISTANCE); // If edge is disabled, assign max possible distance                   	
                }
            }

            for(Edge e: edges){
                if (e.getWeight() < MAX_DISTANCE){
                    graph.addEdge(e.getOne(), e.getTwo(), e.getWeight());
                }
            }

            Dijkstra dijkstra = new Dijkstra(graph, node1);
            return (dijkstra.getDistanceTo(node2));
        }
    }

    /**
     * Exports a piece of code to a text file
     * @param f String filename
     * @param code String code to be exported
     */
    public static void exportTranslation(String f, String code){
        try {
            BufferedWriter out = new BufferedWriter (new FileWriter(f));
            out.write(code);
            out.close();
        }
        catch (IOException e){
            System.out.println("Error exporting PRISM map translation");
        }
    }

}
