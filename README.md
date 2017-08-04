# IPL

## Installation

1) Install the Eclipse Modeling Tools variant of Eclipse: http://www.eclipse.org/downloads/packages/
    (If the latest version fails to work, Neon.3 is known working)
    It is best to avoid using the automated AADL script and install Eclipse components manually. 
    * EMF -- 2.12.0.
    * Xtext Complete SDK (includes MWE 2 Language SDK) -- 2.11.0 or 2.12.0. 
    * Xtext Antlr SDK Feature -- 2.1.1. 
    * Xsemantics -- 2.11.0 or 2.12.0 (consistent with xtext).
    
    Beware of installing several xtext/xbase versions (one included in SDK and one from older repos) and several xtend versions (one comes fadds multiple xtend definitions, confusing the linker). 
    
2) Download and set up the OSATE 2.2 sources: https://wiki.sei.cmu.edu/aadl/index.php/Getting_Osate_2_sources
    Notes: 
    * Ignore the instructions to install Eclipse Mars, newer versions should work.
    * You do not need additional AADL projects from the following repositories: alisa, osate2-ocarina, smaccm, emfta, ErrorModelV2. They can be closed. Only osate2-core is required for IPL. 
    
3) Import this project into Eclipse: File → Import → Git → Projects from Git
