# README #

### SyMC- a Tool for SMT-based Bounded Invariance Checking of Simulink Models. ###

* Quick summary
* V 0.0.1

### Module documentation ###

This section describes the different modules in the code.

CocoSim: whenever there is a folder CoCoSim, that means that classes inside
work with json data structured according to the CoCoSim data format. For
industrial models, we work with CoCoSim.

#### Simulink ####

* Main file: "symc.py"
* Description: "This module is responsible for unfolding the execution of the
Simulink model. The functionality of the module start with class symc.py which
unfolds the model by creating a state-space representation."

#### ModelChecker (older version of the Simulink module) ####

* Main file: "symc.py"
* Description: "This module is responsible for unfolding the execution of the Simulink model
(not including e.g. Stateflow blocks). The functionality of the module start with class
symc.py which unfolds the model by creating a state-space representation."

#### AssertionGenerators ####

* Main file: "assertioninstantiator.py"
* Description: "This module extracts declarations and assertions for a given
Simulink block. The main class assertioninstantiator.py takes a blockpackage as
input, then computes the assertion string corresponding to the given blockpackage.
The class declarationgenerator.py generates declaration strings given a model
and a connection table."

#### Logging ####

* Main file: "logmanager.py"
* Description: "The purpose of this module to provide log features for the
execution of the model."

#### Utils ####

* Main file: "utils.py"
* Description: "This module provides various useful utilities e.g.
'compareStringsIgnoreCase', 'stringify' etc."

#### RoutineGenerators ####

* Main file: "routinegenerator.py"
* Description: "Not used at the moment"

### Observations on the run ###

In this section, I will be documenting the observations from the continuous
execution of the early prototypes.

#### V 0.0.1 ####

* The tool runs pretty decent. For checking a run of 60 seconds of the wheel.json
model, we report the following times:
- model generation time: 1716 seconds.
- model checking (SMT checking) time: 2.15 seconds.
- version moved to branch "dev"

### How do I get set up? ###

* Summary of set up
* Configuration
* Dependencies
* Database configuration
* How to run tests
* Deployment instructions

### Contribution guidelines ###

* Writing tests
* Code review
* Other guidelines

### Contact ###

For any further information feel free to contact me directly.
