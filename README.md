# CoCoMoT
Conformance checking of data Petri nets (DPNs) by an SMT encoding.

## Requirements
The script is written for python3, and requires currently the following:
 * yices bindings 1.1.3 (https://github.com/SRI-CSL/yices2_python_bindings)
 * Z3 bindings (https://github.com/Z3Prover/z3)
 * pm4py (https://pm4py.fit.fraunhofer.de/)

## Usage
Example calls are as follows:
 * $ python3 cocomot.py data/sat_paper/sat_paper_fig2.pnml data/sat_paper/sat_paper_fig2.xes
 * $ python3 cocomot.py data/road_traffic_billing/RoadFines_WithData.pnml data road_traffic_billing/road_fines_27.xes
 * $ python3 cocomot.py data/hospital_billing/Facturatie-Figure_15_6.pnml data/hospital_billing/trace20.xes 

## More data
Complete log files for the road fine, hospital billing, and sepsis data sets are
available:
  * M. de Leoni, F. Mannhardt: Road traffic fine management process
    https://doi.org/10.4121/uuid:270fd440-1057-4fb9-89a9-b699b47990f5
  * F. Mannhardt: Hospital Billing - Event Log
    https://doi.org/10.4121/uuid:76c46b83-c930-4798-a1c9-4be94dfeb741
  * F. Mannhardt: Sepsis Cases - Event Log
    https://doi.org/10.4121/uuid:915d2bfb-7e84-49ad-a286-dc35f063a460
