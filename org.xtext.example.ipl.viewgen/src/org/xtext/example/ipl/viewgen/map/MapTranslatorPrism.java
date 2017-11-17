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
 * @author jcamara
 *
 * Eventually, the MapTranslator might be moved into a more general
 * translator incorporating elements from the architecture model, etc.
 */


public class MapTranslatorPrism extends MapTranslatorUtil {

    public static final String VERSION_STR = "V0.4 - Oct 2017";

    public static final String MODEL_TYPE = "mdp";
    public static final String MODULE_POSTFIX_STR = "_module";	
    public static final String TURN_VARIABLE = "turn";
    public static final String MOVE_CMD_STR = "_to_";
    public static final String MIN_POSTFIX = "_min";
    public static final String MAX_POSTFIX = "_max";
    public static final String INIT_POSTFIX = "_init";
    public static final String UPDATE_POSTFIX = "_upd";
    public static final String HEADING_CONST_PREFIX="H_";
    public static final String ROTATION_TIME_FORMULA_PREFIX="rot_time_";
    public static final String ROTATION_ENERGY_FORMULA_PREFIX="rot_energy_";
    public static final String ENVIRONMENT_TURN_STR = "ET";
    public static final String ROBOT_TURN_STR = "RT";


    // Environment Configuration constants

    public static final String ENVIRONMENT_PLAYER_NAME = "env";
    public static final String ENVIRONMENT_UPDATE_HOUSEKEEPING_STR = " ("+TURN_VARIABLE+"'="+ROBOT_TURN_STR+")";
    public static final String ENVIRONMENT_GUARD_STR = "& (turn="+ENVIRONMENT_TURN_STR+")";

    // Robot Configuration constants

    public static final String ROBOT_PLAYER_NAME = "bot";
    public static final String ROBOT_GUARD_STR = "& (turn="+ROBOT_TURN_STR+")";
    public static final String ROBOT_UPDATE_HOUSEKEEPING_STR = " & ("+TURN_VARIABLE+"'="+ENVIRONMENT_TURN_STR+")";
    public static final String ROBOT_LOCATION_VAR = "l";
    public static final String INITIAL_ROBOT_LOCATION_CONST = "INITIAL_LOCATION";
    public static final String TARGET_ROBOT_LOCATION_CONST = "TARGET_LOCATION";
    public static final String ROBOT_BATTERY_VAR = "b";
    public static final String ROBOT_BATTERY_RANGE_MAX_CONST = "MAX_BATTERY";
    public static final String INITIAL_ROBOT_BATTERY_CONST = "INITIAL_BATTERY";
    public static final String BATTERY_GUARD_STR="& ("+ROBOT_BATTERY_VAR+">="+ROBOT_BATTERY_DELTA+")"; // Not used for the time being (battery depletion condition covered by STOP_GUARD_STR)
    public static final String BATTERY_UPDATE_STR = ROBOT_BATTERY_VAR+UPDATE_POSTFIX;

    public static final String ROBOT_SPEED_VAR = "s";

    public static final String ROBOT_HEADING_VAR = "r";
    public static final String INITIAL_ROBOT_HEADING_CONST = "INITIAL_HEADING";

    public static final String ROBOT_LOC_MODE_VAR = "k";
    public static final String ROBOT_LOC_MODE_LO_CONST = "LOC_LO";
    public static final String ROBOT_LOC_MODE_LO_VAL = "0";
    public static final String ROBOT_LOC_MODE_MED_CONST = "LOC_MED";
    public static final String ROBOT_LOC_MODE_MED_VAL = "1";
    public static final String ROBOT_LOC_MODE_HI_CONST = "LOC_HI";
    public static final String ROBOT_LOC_MODE_HI_VAL = "2";
    public static final boolean ROBOT_LOC_MODE_HI_KINECT = true;
    public static final boolean ROBOT_LOC_MODE_MED_KINECT = true;
    public static final boolean ROBOT_LOC_MODE_LO_KINECT = false;
    public static final String ROBOT_LOC_MODE_MAX_RECONF_CONST = "LOC_MODE_RECONF_MAX";
    public static final String ROBOT_LOC_MODE_RECONF_VAR = "kr";

    // Goal and stop condition configuration constants

    public static final String GOAL_PRED="goal"; // Goal achieved predicate (currently target location reached)
    public static final String GOAL_PRED_DEF=GOAL_PRED+" = "+ROBOT_LOCATION_VAR+"="+TARGET_ROBOT_LOCATION_CONST+";";

    public static final String	STOP_PRED = "stop"; // Stop condition predicate (currently target location reached of insufficient battery to move to a nearby location)
    public static final String	STOP_PRED_DEF = STOP_PRED + " = "+GOAL_PRED+" | "+ROBOT_BATTERY_VAR+"<"+ROBOT_BATTERY_DELTA+";";
    public static final String	STOP_GUARD_STR = "& (!"+STOP_PRED+")";

    public static final String TACTIC_PREFIX="t";

    // Properties' indices
    public static final int TIME_PROPERTY = 0;
    public static final int ACCURACY_PROPERTY = 1;

    /**
     * Generates PRISM model game structure - Alternating Robot/Environment turns
     * @return String a string with the general declarations for PRISM model turn structure
     */
    public static String generateGameStructure(){
        String buf=new String();
        buf+=MODEL_TYPE+"\n\n";
        buf+="const "+ENVIRONMENT_TURN_STR+"=0;\n";
        buf+="const "+ROBOT_TURN_STR+"=1;\n";
        buf+="\nglobal "+TURN_VARIABLE+":["+ENVIRONMENT_TURN_STR+".."+ROBOT_TURN_STR+"] init "+ENVIRONMENT_TURN_STR+";\n\n";		 
        return buf+"\n";
    }


    /**
     * Generates a list of labels for movement commands between locations
     * @return LinkedString<String> list of movement between location command strings 
     * Unused for the time being
     */
    public static LinkedList<String> generateMoveCommandStrs(){
        synchronized (m_map) {
            LinkedList<String> res = new LinkedList<String> ();
            LinkedList<EnvMapArc> arcs = m_map.getArcs();
            for (int i=0; i<arcs.size(); i++){
                res.add(arcs.get(i).getSource()+MOVE_CMD_STR+arcs.get(i).getTarget());
            }
            return res;
        }
    }

    /**
     * Generates labels for robot orientation/heading
     * @return String PRISM encoding for robot orientation constants
     */
    public static String generateHeadingConstants(){
        String buf="// Robot heading/orientation constants\n\n";
        int c=0;
        for (Heading h : Heading.values()) {
            buf+="const "+HEADING_CONST_PREFIX+h.name()+"="+String.valueOf(c)+";\n";
            c++;
        }
        return buf+"\n";
    }

    /**
     * Generates labels for map locations
     * @return String PRISM encoding for map location constants
     */
    public static String generateLocationConstants(){
        String buf="// Map location constants\n\n";
        buf+="const "+INITIAL_ROBOT_LOCATION_CONST+";\n";
        buf+="const "+TARGET_ROBOT_LOCATION_CONST+";\n\n";
        buf+="formula "+GOAL_PRED_DEF+"\n\n";
        buf+="formula "+STOP_PRED_DEF+"\n\n";
        for (Map.Entry<String,EnvMapNode> entry : m_map.getNodes().entrySet() ){
            buf+="const "+entry.getKey()+"="+String.valueOf(entry.getValue().getId())+";\n";
        }
        return buf+"\n";
    }

    /**
     * @return String PRISM encoding for the environment process
     */
    public static String generateEnvironmentModule(){
        String  buf="// Environment process\n\n";
        buf+="module "+ENVIRONMENT_PLAYER_NAME+MODULE_POSTFIX_STR+"\n";
        buf+="end:bool init false;\n\n";
        buf+="\t[] true "+ENVIRONMENT_GUARD_STR +" "+STOP_GUARD_STR+"-> "+ENVIRONMENT_UPDATE_HOUSEKEEPING_STR+";\n";
        buf+="\t[] "+STOP_PRED +"  & !end -> (end'=true);\n";
        buf+="endmodule\n\n";
        return buf;
    }

    /**
     * @return String PRISM encoding for the robot process
     * @param boolean inhibitTactics if true, it does not generate any tactic commands (just movement commands)
     */
    public static String generateRobotModule(boolean inhibitTactics){
        String buf="// Robot process\n\n";
        buf+="const "+ROBOT_BATTERY_RANGE_MAX_CONST+"="+ROBOT_BATTERY_RANGE_MAX+";\n";
        buf+="const "+INITIAL_ROBOT_BATTERY_CONST+";\n";
        buf+="const "+INITIAL_ROBOT_HEADING_CONST+";\n";
        buf+="const "+ROBOT_HALF_SPEED_CONST+"=0;\n";
        buf+="const "+ROBOT_FULL_SPEED_CONST+"=1;\n";
        buf+="const "+ROBOT_LOC_MODE_LO_CONST+"="+ROBOT_LOC_MODE_LO_VAL+";\n";
        buf+="const "+ROBOT_LOC_MODE_MED_CONST+"="+ROBOT_LOC_MODE_MED_VAL+";\n";
        buf+="const "+ROBOT_LOC_MODE_HI_CONST+"="+ROBOT_LOC_MODE_HI_VAL+";\n";   
        buf+="const "+ROBOT_LOC_MODE_MAX_RECONF_CONST+"="+ROBOT_LOC_MODE_MAX_RECONF_VAL+";\n";   

        buf+="\n"+generateBatteryUpdates();
        buf+="module "+ROBOT_PLAYER_NAME+MODULE_POSTFIX_STR+"\n";
        buf+=ROBOT_BATTERY_VAR+":["+ROBOT_BATTERY_RANGE_MIN+".."+ROBOT_BATTERY_RANGE_MAX_CONST+"] init "+INITIAL_ROBOT_BATTERY_CONST+";\n";
        buf+=ROBOT_LOCATION_VAR+":[0.."+m_map.getNodeCount()+"] init "+INITIAL_ROBOT_LOCATION_CONST+";\n";
        buf+=ROBOT_SPEED_VAR+":["+ROBOT_HALF_SPEED_CONST+".."+ROBOT_FULL_SPEED_CONST+"] init "+ROBOT_HALF_SPEED_CONST+";\n";
        buf+=ROBOT_LOC_MODE_VAR+":["+ROBOT_LOC_MODE_LO_CONST+".."+ROBOT_LOC_MODE_HI_CONST+"] init "+ROBOT_LOC_MODE_HI_CONST+";\n";
        buf+=ROBOT_HEADING_VAR+":[0.."+String.valueOf(Heading.values().length)+"] init "+INITIAL_ROBOT_HEADING_CONST+";\n";
        buf+=ROBOT_LOC_MODE_RECONF_VAR+":[0.."+ROBOT_LOC_MODE_MAX_RECONF_VAL+"] init 0;\n";

        buf+="robot_done:bool init false;\n";
        buf+="\t[] true "+ROBOT_GUARD_STR+" "+STOP_GUARD_STR+" & (robot_done) -> (robot_done'=false)"+ROBOT_UPDATE_HOUSEKEEPING_STR+";\n";
        if (!inhibitTactics) {
            buf+="\n"+generateTacticCommands();
        }
        buf+="\n"+generateMoveCommands();
        buf+="endmodule\n\n";
        return buf;

    }

    public static String generateBatteryUpdates(){
        synchronized (m_map) {
            String buf="";
            BatteryPredictor bp = new BatteryPredictor();
            buf+="formula b_upd_charge = min("+ROBOT_BATTERY_VAR+"+"+String.valueOf(Math.round (bp.batteryCharge(ROBOT_CHARGING_TIME)))+", "+ROBOT_BATTERY_RANGE_MAX_CONST+");\n\n";
            for (int i=0;i<m_map.getArcs().size();i++){
                EnvMapArc a = m_map.getArcs().get(i);
                if (!a.isEnabled ()) {
                    continue;
                }
                double t_distance = a.getDistance ();

                String battery_delta_half_speed_lo = getDeltaEnergy(ROBOT_HALF_SPEED_CONST, t_distance, ROBOT_LOC_MODE_LO_CONST);
                String battery_delta_half_speed_med = getDeltaEnergy(ROBOT_HALF_SPEED_CONST, t_distance, ROBOT_LOC_MODE_MED_CONST);
                String battery_delta_half_speed_hi = getDeltaEnergy(ROBOT_HALF_SPEED_CONST, t_distance, ROBOT_LOC_MODE_HI_CONST);

                String battery_delta_full_speed_lo = getDeltaEnergy(ROBOT_FULL_SPEED_CONST, t_distance, ROBOT_LOC_MODE_LO_CONST);
                String battery_delta_full_speed_med = getDeltaEnergy(ROBOT_FULL_SPEED_CONST, t_distance, ROBOT_LOC_MODE_MED_CONST);
                String battery_delta_full_speed_hi = getDeltaEnergy(ROBOT_FULL_SPEED_CONST, t_distance, ROBOT_LOC_MODE_HI_CONST);

                String rote = ROTATION_ENERGY_FORMULA_PREFIX+a.getSource()+MOVE_CMD_STR+a.getTarget();

                String formulaBaseName = BATTERY_UPDATE_STR+"_"+a.getSource()+"_"+a.getTarget();
                buf+="formula " + formulaBaseName + "_" + ROBOT_LOC_MODE_HI_CONST + "= "+ROBOT_SPEED_VAR+"="+ROBOT_HALF_SPEED_CONST+"? max(0,"+ROBOT_BATTERY_VAR+"-("+battery_delta_half_speed_hi+"+"+rote+")) : max(0,"+ROBOT_BATTERY_VAR+"-("+battery_delta_full_speed_hi+"+"+rote+"))" +";\n";    	        
                buf+="formula " + formulaBaseName + "_" + ROBOT_LOC_MODE_MED_CONST + "= "+ROBOT_SPEED_VAR+"="+ROBOT_HALF_SPEED_CONST+"? max(0,"+ROBOT_BATTERY_VAR+"-("+battery_delta_half_speed_med+"+"+rote+")) : max(0,"+ROBOT_BATTERY_VAR+"-("+battery_delta_full_speed_med+"+"+rote+"))" +";\n";    	        
                buf+="formula " + formulaBaseName + "_" + ROBOT_LOC_MODE_LO_CONST + "= "+ROBOT_SPEED_VAR+"="+ROBOT_HALF_SPEED_CONST+"? max(0,"+ROBOT_BATTERY_VAR+"-("+battery_delta_half_speed_lo+"+"+rote+")) : max(0,"+ROBOT_BATTERY_VAR+"-("+battery_delta_full_speed_lo+"+"+rote+"))" +";\n";    	        
                buf += "formula " + formulaBaseName + " = " + ROBOT_LOC_MODE_VAR +" = "+ ROBOT_LOC_MODE_LO_CONST + " ? " + formulaBaseName + "_" + ROBOT_LOC_MODE_LO_CONST +" : ( " + ROBOT_LOC_MODE_VAR +" = "+ ROBOT_LOC_MODE_MED_CONST + " ? " + formulaBaseName + "_" + ROBOT_LOC_MODE_MED_CONST  + " : " + formulaBaseName + "_" + ROBOT_LOC_MODE_HI_CONST+" );\n" ;

            }
            return buf+"\n";
        }
    }


    /**
     * Generates PRISM encoding for movement commands between locations in the robot module
     * @return String encoding between location command strings 
     */
    public static String generateMoveCommands(){
        synchronized (m_map) {
            String buf="";
            for (int i=0;i<m_map.getArcs().size();i++){
                EnvMapArc a = m_map.getArcs().get(i);
                if (a.isEnabled()){
                    String kGuard="";
                    if (a.getDistance() > MAXIMUM_KINECT_OFF_DISTANCE_VAL) {
                        kGuard ="& ("+ROBOT_LOC_MODE_VAR+"!="+ROBOT_LOC_MODE_LO_CONST+") ";
                    }
                    buf+="\t ["+a.getSource()+MOVE_CMD_STR+a.getTarget()+"] ("+ROBOT_LOCATION_VAR+"="+a.getSource()+") "+
                    		kGuard+STOP_GUARD_STR+" "+ROBOT_GUARD_STR+" & (!robot_done) -> ("+
                    		ROBOT_LOCATION_VAR+"'="+a.getTarget()+") "+" & ("+ROBOT_BATTERY_VAR+"'="+
                    		BATTERY_UPDATE_STR+"_"+a.getSource()+"_"+a.getTarget()+")"+ " & ("+
                    		ROBOT_HEADING_VAR+"'="+HEADING_CONST_PREFIX + findArcHeading(a).name() + 
                    		") & (robot_done'=true);\n";                	
                }
            }
            return buf+"\n";		
        }
    }

    /**
     * Returns PRISM encoding for robot module tactics
     * @return
     */
    public static String generateTacticCommands(){
        String buf="";
        buf += generateSpeedTacticCommands();
        buf += generateSensingTacticCommands();
        buf += generateChargingTacticCommands();
        return buf;
    }

    /**
     * Returns PRISM encoding for robot module tactics (Sensing)
     * @return
     */
    public static String generateSensingTacticCommands(){
        String reconfGuard = "& ("+ROBOT_LOC_MODE_RECONF_VAR+"<"+ROBOT_LOC_MODE_MAX_RECONF_CONST+") ";
        String reconfUpdate = "& ("+ROBOT_LOC_MODE_RECONF_VAR+"'="+ROBOT_LOC_MODE_RECONF_VAR+"+1) ";
        String buf="\t // Sensing tactics (lo=kinect off, med=kinect on+low cpu+low accuracy, hi=kinect on+high cpu+high accuracy\n";
        buf+="\t [t_set_loc_lo] ("+ROBOT_LOC_MODE_VAR+"!="+ROBOT_LOC_MODE_LO_CONST+") "+ reconfGuard +STOP_GUARD_STR+" "+ROBOT_GUARD_STR+" & (!robot_done) ->  ("+ROBOT_LOC_MODE_VAR+"'="+ROBOT_LOC_MODE_LO_CONST+")"+ reconfUpdate +" & (robot_done'=true);\n";                	
        buf+="\t [t_set_loc_med] ("+ROBOT_LOC_MODE_VAR+"!="+ROBOT_LOC_MODE_MED_CONST+") "+ reconfGuard +STOP_GUARD_STR+" "+ROBOT_GUARD_STR+" & (!robot_done) ->  ("+ROBOT_LOC_MODE_VAR+"'="+ROBOT_LOC_MODE_MED_CONST+")"+ reconfUpdate + " & (robot_done'=true);\n";                	
        buf+="\t [t_set_loc_hi] ("+ROBOT_LOC_MODE_VAR+"!="+ROBOT_LOC_MODE_HI_CONST+") "+ reconfGuard + STOP_GUARD_STR+" "+ROBOT_GUARD_STR+" & (!robot_done) ->  ("+ROBOT_LOC_MODE_VAR+"'="+ROBOT_LOC_MODE_HI_CONST+")"+ reconfUpdate + " & (robot_done'=true);\n";                	
        return buf+"\n";
    }

    /**
     * Returns PRISM encoding for robot module tactics (Speed)
     * @return
     */
    public static String generateSpeedTacticCommands(){
        String buf="\t // Speed setting change tactics\n";
        buf+="\t [t_set_half_speed] ("+ROBOT_SPEED_VAR+"!="+ROBOT_HALF_SPEED_CONST+") "+STOP_GUARD_STR+" "+ROBOT_GUARD_STR+" & (!robot_done) ->  ("+ROBOT_SPEED_VAR+"'="+ROBOT_HALF_SPEED_CONST+")"+" & (robot_done'=true);\n";                	
        buf+="\t [t_set_full_speed] ("+ROBOT_SPEED_VAR+"!="+ROBOT_FULL_SPEED_CONST+") "+STOP_GUARD_STR+" "+ROBOT_GUARD_STR+" & (!robot_done) ->  ("+ROBOT_SPEED_VAR+"'="+ROBOT_FULL_SPEED_CONST+")"+" & (robot_done'=true);\n";                	
        return buf+"\n";
    }

    /**
     * Returns PRISM encoding for robot module tactics (Charging)
     * @return
     */
    public static String generateChargingTacticCommands(){
        String guard_can_charge=" & (false";
        synchronized(m_map){
            for (Map.Entry<String, EnvMapNode> e: m_map.getNodes().entrySet()){
                if (e.getValue().isChargingStation()){
                    guard_can_charge +="|"+ROBOT_LOCATION_VAR+"="+e.getValue().getId();

                }	
            }
            guard_can_charge+=") & ("+ROBOT_BATTERY_VAR+"<1500*"+String.valueOf(BatteryPredictor.m_battery_scaling_factor)+")";	//TODO: refine this constraint
        }

        String buf="\t // Recharge tactics\n";
        buf+="\t [t_recharge] true "+ guard_can_charge +STOP_GUARD_STR+" "+ROBOT_GUARD_STR+" & (!robot_done) ->  ("+ROBOT_BATTERY_VAR+"'=b_upd_charge"+")"+" & (robot_done'=true);\n";                	
        return buf+"\n";
    }

    /**
     * @return String PRISM encoding for time rewards associated with an EnvMap
     * @param inhibitTactics boolean if true, it does not generate rewards associated with tactics
     */
    public static String generateTimeReward(boolean inhibitTactics){
        synchronized (m_map) {
            String buf="rewards \"time\"\n";
            NumberFormat f = new DecimalFormat("#0.0000");

            if (!inhibitTactics){
                buf+="\t[t_set_half_speed] true : "+String.valueOf(DEFAULT_TIME_TACTIC_TIME)+";\n";
                buf+="\t[t_set_full_speed] true : "+String.valueOf(DEFAULT_TIME_TACTIC_TIME)+";\n";
                buf+="\t[t_set_loc_lo] true : "+String.valueOf(DEFAULT_TIME_TACTIC_TIME)+";\n";
                buf+="\t[t_set_loc_med] true : "+String.valueOf(DEFAULT_TIME_TACTIC_TIME)+";\n";
                buf+="\t[t_set_loc_hi] true : "+String.valueOf(DEFAULT_TIME_TACTIC_TIME)+";\n";
                buf+="\t[t_recharge] true : "+String.valueOf(ROBOT_CHARGING_TIME)+";\n";
            }
            for (int i=0;i<m_map.getArcs().size();i++){
                EnvMapArc a = m_map.getArcs().get(i);
                if (a.isEnabled()) {
                    double t_distance = a.getDistance (); //  float(self.get_transition_attribute_value(t,"distance"))
                    String t_time_half_speed=f.format(SpeedPredictor.moveForwardTimeSimple(t_distance, ROBOT_HALF_SPEED_CONST));
                    String t_time_full_speed=f.format(SpeedPredictor.moveForwardTimeSimple(t_distance, ROBOT_FULL_SPEED_CONST));
                    String t_time_dr_speed=f.format(SpeedPredictor.moveForwardTimeSimple(t_distance, ROBOT_DR_SPEED_CONST));

                    String action_name = a.getSource()+MOVE_CMD_STR+a.getTarget();
                    String drs = ROBOT_LOC_MODE_VAR +" = "+ROBOT_LOC_MODE_LO_CONST+" ? "+ t_time_dr_speed + " + " + ROTATION_TIME_FORMULA_PREFIX+action_name + " : " ;
                    buf+="\t["+action_name+"] true :" + drs + ROBOT_SPEED_VAR+"="+ROBOT_HALF_SPEED_CONST+"? "+t_time_half_speed+" + "+ROTATION_TIME_FORMULA_PREFIX+action_name+" : "+t_time_full_speed+" + "+ROTATION_TIME_FORMULA_PREFIX + action_name+";\n";
                }
            }
            buf+="endrewards\n\n";
            return buf;
        }
    }


    /**
     * @return PRISM encoding for all rotation formulas (for all arcs in map)
     */
    public static String generateRotationTimeFormulas(){
        String buf="// Rotation time formulas for map arcs\n";
        synchronized (m_map) {
            for (int i=0;i<m_map.getArcs().size();i++){
                EnvMapArc a = m_map.getArcs().get(i);
                if (a.isEnabled()) {
                    buf = buf+generateRotationTimeFormulaForArc(a);
                }
            }
        }
        return buf +"\n";
    }

    public static String generateRotationEnergyFormulas(){
        String buf="// Rotation time formulas for map arcs\n";
        synchronized (m_map) {
            for (int i=0;i<m_map.getArcs().size();i++){
                EnvMapArc a = m_map.getArcs().get(i);
                if (a.isEnabled()) {
                    buf = buf+generateRotationEnergyFormulaForArc(a);
                }
            }
        }
        return buf +"\n";
    }

    /**
     * Generates the PRISM encoding (as a formula) for all possible rotation times 
     * (for every heading in MissionState.Heading), given a map arc a
     * @param a Map arc
     * @return PRISM encoding for rotation times in arc a
     */
    public static String generateRotationTimeFormulaForArc(EnvMapArc a){
        NumberFormat f = new DecimalFormat ("#0.0000");
        String buf="formula "+ROTATION_TIME_FORMULA_PREFIX+a.getSource()+MOVE_CMD_STR+a.getTarget()+" = ";
        for (Heading h : Heading.values()) {
            buf += ROBOT_HEADING_VAR + "=" + HEADING_CONST_PREFIX + h.name() + " ? " + f.format (getRotationTime(Heading.convertToRadians(h),a)) + " : ";
        }
        buf+=" 0;\n";
        return buf;
    }

    public static String generateRotationEnergyFormulaForArc(EnvMapArc a){
        NumberFormat f = new DecimalFormat ("#0");
        String buf="formula "+ROTATION_ENERGY_FORMULA_PREFIX+a.getSource()+MOVE_CMD_STR+a.getTarget()+" = ";
        for (Heading h : Heading.values()) {
            buf += ROBOT_HEADING_VAR + "=" + HEADING_CONST_PREFIX + h.name() + " ? " + f.format (BatteryPredictor.batteryConsumption(ROBOT_HALF_SPEED_CONST, true, ROBOT_LOC_MODE_MED_KINECT, ROBOT_LOC_MODE_HI_CPU_VAL, getRotationTime(Heading.convertToRadians(h),a))) + " : ";
        }
        buf+=" 0;\n";
        return buf;
    }

    /**
     * Translates a path into a PRISM module constraining the movements of the robot to that path
     * @param path List of strings with the locations of the path from source to target (e.g., ["ls", ..., "l1"])
     * @return String PRISM encoding of the path constraint module
     */
    public static String generatePathConstraintModule(List path){
        String buf="\n"+"module path_constraint\n";
        LinkedList<String> allowed = new LinkedList<String>();
        for (int i=0; i< path.size()-1; i++){
            allowed.add(path.get(i)+ MOVE_CMD_STR + path.get(i+1));
        }
        buf+= "// Allowed arcs: "+ String.valueOf(allowed) + "\n";
        synchronized(m_map) {
            for (EnvMapArc a : m_map.getArcs()){
                String str_arc= a.getSource() + MOVE_CMD_STR + a.getTarget();
                if (!allowed.contains(str_arc)) {
                    buf += "\t[" + str_arc + "] false -> true; \n";
                }
            }
        }
        buf += "endmodule\n";
        return buf;
    }

    /**
     * Translates a plan into a PRISM module constraining the action of the robots to that plan00
     * @param plan List of strings (e.g., ["l1_to_l2", ..., "t_recharge", ..., "l4_to_l5"])
     * @return String PRISM encoding of the plan constraint module
     */
    public static String generatePlanConstraintModule(List<String> plan){
        LinkedList<String> allTactics = new LinkedList<String>(Arrays.asList("t_set_loc_lo", "t_set_loc_med", "t_set_loc_hi", "t_set_half_speed", "t_set_full_speed", "t_recharge"));

        String buf="\n"+"module plan_constraint\n";
        buf+= "pc_s : [0.."+String.valueOf(plan.size())+"] init 0;\n";
        for (int i=0; i< plan.size(); i++){
            buf += "\t["+plan.get(i)+"] (pc_s="+String.valueOf(i)+") -> (pc_s'="+String.valueOf(i+1)+"); \n";
        }

        LinkedList<String> allowed = new LinkedList<String>();
        for (int i=0; i< plan.size(); i++){
            String action = plan.get(i);
            String[] e = action.split("_");
            if (!Objects.equals(MapTranslatorPrism.TACTIC_PREFIX, e[0])) {
                allowed.add(plan.get(i));
            } 
        }
        buf+="\t // Disallowed tactics\n";
        for (int i=0; i< allTactics.size(); i++){
            String action = allTactics.get(i);
            if (!plan.contains(action)) {
                buf += "\t[" + action + "] false -> true; \n";
            }
        }

        buf+= "\t // Allowed arcs: "+ String.valueOf(allowed) + "\n";
        buf+="\t // Disallowed arcs\n";
        synchronized(m_map) {
            for (EnvMapArc a : m_map.getArcs()){
                String str_arc= a.getSource() + MOVE_CMD_STR + a.getTarget();
                if (!allowed.contains(str_arc)) {
                    buf += "\t[" + str_arc + "] false -> true; \n";
                }
            }
        }

        buf += "endmodule\n";
        return buf;
    }


    /**
     * @return String PRISM encoding for distance rewards between nodes in the map
     */
    public static String generateDistanceReward(){
        synchronized (m_map) {
            NumberFormat f = new DecimalFormat ("#0.0000");
            String buf="rewards \"distance\"\n";

            for (Map.Entry<String,EnvMapNode> entry : m_map.getNodes().entrySet() ){
                String v = entry.getKey();

                buf+="\t"+STOP_PRED+" & "+TARGET_ROBOT_LOCATION_CONST+"="+v+" : ";

                for (Map.Entry<String,EnvMapNode> entry2 : m_map.getNodes().entrySet() ){
                    String v2 = entry2.getKey();
                    if (!v2.equals(v)){
                        buf += ROBOT_LOCATION_VAR + "=" + v2 + " ? " + f.format (shortestPathDistance (v, v2)) + " : ";
                    }
                }
                buf+=" 0;\n";

            }
            buf+="endrewards\n\n";
            return buf;		
        }
    }


    /**
     * Generates the PRISM specification for an adaptation scenario, based on a given EnvMap
     * @param inhibitTactics boolean if true, it generates a specification only with move actions, disabling the rest of actions and tactics
     * @return String PRISM encoding for adaptation scenario
     */

    public static String getMapTranslation(){
        return getMapTranslation(false);
    }


    public static String getMapTranslation(boolean inhibitTactics){
        String buf="// Generated by BRASS MARS Robot Map PRISM Translator "+VERSION_STR+".\n\n";
        buf+=generateGameStructure()+"\n";
        buf+=generateHeadingConstants()+"\n";
        buf+=generateLocationConstants()+"\n";
        buf+=generateEnvironmentModule()+"\n";
        buf+=generateRobotModule(inhibitTactics)+"\n";
        buf+=generateTimeReward(inhibitTactics)+"\n";
        buf+=generateRotationTimeFormulas()+"\n";
        buf+=generateRotationEnergyFormulas()+"\n";
        buf+=generateDistanceReward()+"\n";
        buf+="// --- End of generated code ---\n";
        return buf;
    }

    /**
     * Generates the PRISM specification for an adaptation scenario, constrained to a specific path of robot movements
     * @param path List of strings containing the sequence of locations in the path, e.g., ["l1", ..., "l8"]
     * @return String PRISM encoding for constrained adaptation scenario
     */
    public static String getConstrainedToPathMapTranslation(List<String> path){
        return getConstrainedToPathMapTranslation(path, false);
    }

    public static String getConstrainedToPathMapTranslation(List<String> path, boolean inhibitTactics){
        return getMapTranslation(inhibitTactics) +"\n\n"+ generatePathConstraintModule(path);
    }

    /**
     * Generates the PRISM specification for an adaptation scenario, constrained to a specific plan
     * @param path List of strings containing the sequence of actions for the plan (e.g., ["l1_to_l2", ..., "t_recharge", ..., "l4_to_l5"])
     * @return String PRISM encoding for constrained adaptation scenario
     */
    public static String getConstrainedToPlanMapTranslation(List<String> plan){
        return getMapTranslation() +"\n\n"+ generatePlanConstraintModule(plan);
    }

    /**
     * Generates and exports the PRISM specification for an adaptation scenario to a text file
     * @param f String filename to export PRISM specification (constrained to a path)
     * @param path List of strings containing the sequence of locations in the path, e.g., ["l1", ..., "l8"]
     */
    public static void exportMapTranslation(String f, List<String> path) {
        exportMapTranslation (f, path, false);
    }

    public static void exportMapTranslation(String f, List<String> path, boolean inhibitTactics) {
        exportTranslation(f, getConstrainedToPathMapTranslation(path, inhibitTactics));
    }

    /**
     * Generates and exports the PRISM specification for an adaptation scenario to a text file
     * @param f String filename to export PRISM specification (constrained to a plan)
     * @param plan String list with action sequence (e.g., ["l1_to_l2", ..., "t_recharge", ..., "l4_to_l5"])
     */
    public static void exportConstrainedToPlanMapTranslation(String f, List<String> plan) {
        exportTranslation(f, getConstrainedToPlanMapTranslation(plan));
    }

    /**
     * Generates and exports the PRISM specification for an adaptation scenario to a text file
     * @param f String filename to export PRISM specification
     */
    public static void exportMapTranslation(String f){
        exportTranslation(f, getMapTranslation());
    }

    public static void exportMapTranslation(String f, boolean inhibitTactics){
        exportTranslation(f, getMapTranslation(inhibitTactics));
    }

    /**
     * Generates PRISM encoding variants constrained by all non-cyclic paths between two locations
     * @param f_base String base for PRISM models filenames (e.g., target folder)
     * @param source String label of source location
     * @param target String label of target location
     * @return
     */
    public static Map<List, String> exportConstrainedTranslationsBetween(String f_base, String source, String target) {
        return exportConstrainedTranslationsBetween(f_base, source, target, false);   
    }

    public static Map<List, String> exportConstrainedTranslationsBetween(String f_base, String source, String target, boolean inhibitTactics) {
        List<Stack> paths = goFindAllPaths(source, target);
        Map<List, String> specifications = new HashMap<List, String>();
        int c=0;
        for ( List path : paths )  {
            String filename = f_base + "/" + String.valueOf (c);
            exportMapTranslation (filename, path, inhibitTactics);
            specifications.put(path, filename);
            c++;
        }
        return specifications;
    }

    /**
     * Class test
     * @param args
     */
    public static void main(String[] args) {
//        setMap(new EnvMap (/*null,*/ null));
        //dummyMap.insertNode("newnode", "l1", "l2", 17.0, 69.0);
        //setMap(dummyMap);
    	// PRISM generation
//        System.out.println(getMapTranslation()); // Class test
//        exportMapTranslation("/home/ivan/Dropbox/cmu/research/ipl/IPLExamples/IPLRobotProp/model/prism/prism-out.prism", false);
    	
    	
		String mapPath = "/home/ivan/Dropbox/cmu/research/ipl/IPLExamples/IPLRobotProp/model/map/";
		String prismPath = "/home/ivan/Dropbox/cmu/research/ipl/IPLExamples/IPLRobotProp/model/prism/";
		// map names -> scaling factors
		Map<String, Double> maps2Scaling = new HashMap<String, Double>();
		maps2Scaling.put("map1", 1.0);
		maps2Scaling.put("map2", 1.0);
		maps2Scaling.put("map3b", 5.0);
		
		for (String mapName : maps2Scaling.keySet()) {
			// awkward historic scaling factors: map0 & map1 & map2 with 1, map3a/b with 5. 
			// cannot generate for map0 or map3a because missing input data
			BatteryPredictor.m_battery_scaling_factor = maps2Scaling.get(mapName); 
			
			PropertiesConnector.DEFAULT.setProperty(PropertiesConnector.MAP_PROPKEY,
					mapPath + mapName + ".json");
			setMap(new EnvMap(/* null, */ null));

			String fileFullName = "prism_gen_" + mapName;
			exportTranslation(prismPath + fileFullName + ".prism", getMapTranslation());

		}
    }
}
