# IPL: an Integration Property Language for Multiple Models

## Development build setup 

1) Download and install the Eclipse Modeling Tools variant of Eclipse: http://www.eclipse.org/downloads/packages. If the latest version fails to work, Neon.3 is known to work. You will need Java 1.8+. 

2) Install the following Eclipse components. It is best to avoid using the automated AADL script and install Eclipse components manually.
    * EMF -- 2.12.0.
    * Xtext Complete SDK (includes MWE 2 Language SDK) -- 2.11.0 or 2.12.0.
    * Xtext Antlr SDK Feature -- 2.1.1.
    * Xsemantics -- 2.11.0 or 2.12.0 (consistent with xtext).
    
    Beware of installing several xtext/xbase versions (one included in SDK and one from older repos) and several xtend versions (they provide multiple xtend definitions, confusing the linker). 
    
3) Download and set up the OSATE 2.2.? sources: https://wiki.sei.cmu.edu/aadl/index.php/Getting_Osate_2_sources
    Notes: 
    * The osate2-core project is necessary and sufficient. Commit 274b1ced2 is known to work with the current version of IPL. You do not need additional AADL projects from the following repositories: alisa, osate2-ocarina, smaccm, emfta, ErrorModelV2. They can be closed or deleted. 
    * Ignore the instructions to install Eclipse Mars, newer versions should work.
    
4) Import this project into Eclipse: File → Import → Git → Projects from Git. 
    * It along comes with its major dependencies: z3 SMT solver and Prism model checker. 
    * z3 comes with a binary in org.xtext.example.ipl.z3, which is directly called by IPL. You can replace this binary with a different verion. 
    * All the Prism model checker dependencies (including static and shared libraries) are provided in the ipl.prism.lib project. IPL is known to work with the version 4.4.beta of Prism. If you wish to adjust them, change variables LD_LIBRARY_PATH (should point to share library \*.so files) and PRISM_LIB_PATH (should point to the HOA script and a jar of the Rabinizer tool). 

5) Build the IPL language infrastructure by running org.xtext.example.ipl/src/org/xtext/example/ipl/GenerateIPL.mwe2 script (Right-Click on the file -> Run as -> MWE2 Workflow). Refresh and clean all the projects. It should build automatically. 

6) Use the provided launch file "IPL Eclipse Application.launch" to start an Eclipse version with IPL support.

7) Download the IPL examples and import them in the launched verion of the Eclipse. 

8) Build \*.ipl files to perform verification of integration properties. It is recommended that you turn off automatic building and target specific files since verification can take some time. 

9) If you want to generate AADL views or Prism models from json maps, run the main methods in org.xtext.example.ipl.viewgen/src/org/xtext/example/ipl/viewgen/map/MapTranslatorAadl.java and /org.xtext.example.ipl.viewgen/src/org/xtext/example/ipl/viewgen/map/MapTranslatorPrism.java, respectively. 
	* Their launch files are also provided with in the repository. 
	* You will need to adjust paths in the environment variables for these generators. MAP_DIR should point to the directory with input maps. PRISM_OUT_DIR and AADL_OUT_DIR should point to the directories where generated Prism and AADL models are put, respectively. None of these paths should end with a '/'. 

## User build setup

TBA.
