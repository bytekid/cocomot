# CoCoMoT
Conformance checking of data Petri nets (DPNs) by an SMT encoding.

## Requirements
The script is written for python3, and requires currently the following:
 * yices bindings (https://github.com/SRI-CSL/yices2_python_bindings)
 * Z3 bindings (https://github.com/Z3Prover/z3)
 * pm4py v2.2.19.2 (https://pm4py.fit.fraunhofer.de/)

## Usage

### Basic calls
Example calls are as follows:  
 `$ python3 src/cocomot.py data/sat_paper/sat_paper_fig2.pnml data/sat_paper/sat_paper_fig2.xes`  
For verbose output (i.e., to obtain the alignment), add option `-v`:  

 `$ python3 src/cocomot.py data/hospital_billing/Facturatie-Figure_15_6.pnml data/hospital_billing/trace20.xes -v`

In order to process a log in parallel, you can also add an argument specifying
the number of processes to be used (`-n`):  

 `$ python3 src/cocomot.py -d data/road_traffic_billing/RoadFines_WithData.pnml -l data/road_traffic_billing/road_fines_27.xes -n 4`

### Uncertainty
CoCoMoT also supports conformance checking of logs with uncertainty, using the 
option `-u` with either `real` or 'like' as arguments. For example, the call  

 `$ python3 src/cocomot.py -d tests/test2/net.pnml -l tests/test2/trace8_fit_2.xes -u like`  

processes a trace with uncertainty. Finally, the tests in the test/ directory
can be run as follows:  

 `$ python3 src/test.py`

## Data and Experiments

### Experiments with uncertainty
Experimental data for cocomot with uncertainty can be found on [this website](http://cl-informatik.uibk.ac.at/users/swinkler/cocomot/uncertainty).

### Data sets
Complete log files for the road fine, hospital billing, and sepsis data sets are
available:
  * M. de Leoni, F. Mannhardt: Road traffic fine management process
    https://doi.org/10.4121/uuid:270fd440-1057-4fb9-89a9-b699b47990f5
  * F. Mannhardt: Hospital Billing - Event Log
    https://doi.org/10.4121/uuid:76c46b83-c930-4798-a1c9-4be94dfeb741
  * F. Mannhardt: Sepsis Cases - Event Log
    https://doi.org/10.4121/uuid:915d2bfb-7e84-49ad-a286-dc35f063a460
