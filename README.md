# IPL: an Integration Property Language for Multiple Models

## Development build setup 

Prerequisites to have before installing IPL: Java 1.8 

Prerequisites to be installed: Eclipse Oxygen 4.7.1a, EMF 2.13.0, Xtext SDK 2.12.0, OSATE 2.3.0.

1) Download an appropriate [Eclipse Installer](https://wiki.eclipse.org/Eclipse_Installer) for your system. 

2) Choose advanced setup and Eclipse Modeling Tools - Oxygen 1a (4.7.1a). It is likely that IPL would work with later releases of Oxygen too. 

3) On the Projects page, add the [setup URL for OSATE 2.3.0](https://raw.githubusercontent.com/osate/osate2-core/2.3.0-RELEASE/osate.releng/osate2.setup) and click through the rest of the dialog. It will install Xtext, OSATE, and many relevant dependencies. You can also use the latest [OSATE setup URL](https://raw.githubusercontent.com/osate/osate2-core/develop/osate.releng/osate2.setup) at your own risk.

Steps 1-3 are also described in more detail with minor deviations (a different install URL) on the [OSATE2 setup page](http://osate.org/setup-development.html).

4) Import this project into Eclipse: File → Import → Git → Projects from Git. 
    * It along comes with its major dependencies: z3 SMT solver and Prism model checker. 
    * z3 comes with a binary in org.xtext.example.ipl.z3, which is directly called by IPL. You can replace this binary with a different verion. 
    * All the Prism model checker dependencies (including static and shared libraries) are provided in the ipl.prism.lib project. IPL is known to work with the version 4.4.beta of Prism. If you wish to adjust them, change variables LD_LIBRARY_PATH (should point to share library \*.so files) and PRISM_LIB_PATH (should point to the HOA script and a jar of the Rabinizer tool). 

5) Build the IPL language infrastructure by running the GenerateIPL run configuration. Alternatively, you can directly run the  org.xtext.example.ipl/src/org/xtext/example/ipl/GenerateIPL.mwe2 script (Right-Click on the file -> Run as -> MWE2 Workflow). Refresh and clean all the projects. It should build automatically. 

6) Use the provided launch file "IPL Eclipse Application" run configuration to start an Eclipse version with IPL support.

7) Download [IPL examples](https://github.com/bisc/IPLExamples) and import them in the launched verion of the Eclipse.

8) To run IPL verification, you can click the IPL verification button while a .ipl file is open or selected. Alternatively, you can use the native Eclipse build. It is recommended that you turn off automatic building and target specific files since verification can take some time. 

9) If you want to generate AADL views or Prism models from json maps, run the main methods in org.xtext.example.ipl.viewgen/src/org/xtext/example/ipl/viewgen/map/MapTranslatorAadl.java and /org.xtext.example.ipl.viewgen/src/org/xtext/example/ipl/viewgen/map/MapTranslatorPrism.java, respectively. 
	* Their launch files are also provided with in the repository. 
	* You will need to adjust paths in the environment variables for these generators. MAP_DIR should point to the directory with input maps. PRISM_OUT_DIR and AADL_OUT_DIR should point to the directories where generated Prism and AADL models are put, respectively. None of these paths should end with a '/'. 

## User build setup

TBA.

## Contacts
 * Ivan Ruchkin iruchkin@cs.cmu.edu
 * Grant Iraci grantira@buffalo.edu
 * Josh Sunshine sunshine@cs.cmu.edu
 * Bradley Schmerl schmerl@cs.cmu.edu
 * David Garlan garlan@cs.cmu.edu
