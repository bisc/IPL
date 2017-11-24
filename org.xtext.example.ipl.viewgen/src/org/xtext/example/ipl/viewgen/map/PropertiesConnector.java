package org.xtext.example.ipl.viewgen.map;

import java.util.Properties;

public class PropertiesConnector {

    public static final String PRISM_ADV_EXPORT_PROPKEY = "prism.adv.export";
    public static final String PRISM_PARAMETERS_PROPKEY = "prism.parameters";
    public static final String PRISM_PROPERTIES_PROPKEY = "prism.properties";
    public static final String PRISM_MODEL_PROPKEY = "prism.model";
    public static final String PRISM_BIN_PROPKEY = "prism.bin";
    public static final String MAP_DIR_PROPKEY = "customize.mapdir.json"; // shared across maps
    public static final String MAP_NAME_PROPKEY = "customize.mapname.json"; // set individually for each map
    public static final String PRISM_OUTPUT_DIR_PROPKEY         = "prism.tmpdir";
    public static final String AADL_OUTPUT_DIR_PROPKEY         = "aadl.tmpdir";

    public static final Properties DEFAULT = new Properties ();

    static {
    	// To use standalone Prism generation (outside of Rainbow), set the environment variables below in your system
    	// e.g. .bashrc or .profile
    	String prismOutDir = System.getenv("PRISM_OUT_DIR"); // e.g., "/Users/jcamara/Dropbox/Documents/Work/Projects/BRASS/rainbow-prototype/trunk/rainbow-brass/prismtmp/";
    	String aadlOutDir = System.getenv("AADL_OUT_DIR");
    	String mapDir = System.getenv("MAP_DIR");
    	
    	if (prismOutDir == null || aadlOutDir == null ) //|| prismBin == null)
    		System.out.println("Failed to initialize the default properties connector: environment variables not set");
    	
        DEFAULT.setProperty (PRISM_MODEL_PROPKEY, prismOutDir + "prismtmp.prism");
        DEFAULT.setProperty (PRISM_PROPERTIES_PROPKEY, prismOutDir + "mapbot.props");
        DEFAULT.setProperty (PRISM_PARAMETERS_PROPKEY, "INITIAL_BATTERY=30000,INITIAL_HEADING=1");
        DEFAULT.setProperty (PRISM_ADV_EXPORT_PROPKEY, prismOutDir + "botpolicy.adv");
        DEFAULT.setProperty (MAP_DIR_PROPKEY, mapDir);
        DEFAULT.setProperty (MAP_NAME_PROPKEY, "map.json"); // just a default name
        DEFAULT.setProperty (PRISM_OUTPUT_DIR_PROPKEY, prismOutDir);
        DEFAULT.setProperty (AADL_OUTPUT_DIR_PROPKEY, aadlOutDir);
    }


}
