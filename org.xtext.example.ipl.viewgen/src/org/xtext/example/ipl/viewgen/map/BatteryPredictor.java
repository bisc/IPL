package org.xtext.example.ipl.viewgen.map;

import java.util.Objects;

import org.xtext.example.ipl.viewgen.map.MapTranslatorPrism;

// To be relocated

/**
 * @author jcamara
 *
 */
public class BatteryPredictor {

	public static /*final*/ double m_battery_scaling_factor = 1.0; // = 5.0;
	
	// battery consumption for moving straight
	public static double batteryConsumption (String speed, String sensing, double time){
		
		// default values if sensing is not set
		boolean kinectEnabled = MapTranslatorPrism.ROBOT_LOC_MODE_HI_KINECT;
		double cpuAvgUsage= MapTranslatorPrism.ROBOT_LOC_MODE_HI_CPU_VAL;
		
		if (Objects.equals(sensing, MapTranslatorPrism.ROBOT_LOC_MODE_MED_CONST)){
			kinectEnabled = MapTranslatorPrism.ROBOT_LOC_MODE_MED_KINECT;
			cpuAvgUsage = MapTranslatorPrism.ROBOT_LOC_MODE_MED_CPU_VAL;
		}

		if (Objects.equals(sensing, MapTranslatorPrism.ROBOT_LOC_MODE_LO_CONST)){
			kinectEnabled = MapTranslatorPrism.ROBOT_LOC_MODE_MED_KINECT;
			cpuAvgUsage = MapTranslatorPrism.ROBOT_LOC_MODE_MED_CPU_VAL;
		}
		
		return batteryConsumption (speed, false, kinectEnabled, cpuAvgUsage, time);
	}
	
    /**
     * Returns the amount of energy consumed (in mWh) when the robot moves at a given speed
     * @param speed String constant (HALF_SPEED or FULL_SPEED for the time being)
     * @param time amount of seconds during which the robot moves.
     * @return
     */
	public static double batteryConsumption (String speed, boolean rotating, boolean kinectEnabled, double cpuAvgUsage, double time) {
        double base_consumption=0;
        double kinect_consumption=0;
        double nuc_consumption=0;
        
        if (Objects.equals(speed, MapTranslatorPrism.ROBOT_HALF_SPEED_CONST))
            base_consumption = 1.674f * time+287.5f;
        if (Objects.equals(speed, MapTranslatorPrism.ROBOT_FULL_SPEED_CONST)) 
        	base_consumption = 3.89f * time+582.6f;
        if (rotating)
        	base_consumption = 4.9f * time + 699f;
        
        if (kinectEnabled)
        	kinect_consumption = 1.426f * time;
        else 
        	kinect_consumption = 0.07f * time;

        nuc_consumption = ( 0.032f * cpuAvgUsage + 1.925f) * time;
        
        return m_battery_scaling_factor * (base_consumption + kinect_consumption + nuc_consumption);
    }
    
    /**
     * Returns the amount of battery recharged (in mWh) for a given time lapse
     * @param time amount in seconds that the rogot stays in the charging base
     * @return
     */
    public double batteryCharge (double time){
    	return m_battery_scaling_factor * 8.35 * time; 
    }

}
