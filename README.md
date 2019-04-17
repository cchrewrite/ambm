# Abstract Machine Batch Modification

This repository contains the source code of the Abstract Machine Batch Modification algorithm. It is built to support the review of the paper: 
#### Automated Abstract Machine Modification Using Semantic Probabilities and Predicate Reconstitution
Due to the double-blind peer review process, authors' names are hidden.

## Installation
1. Install Ubuntu 16.04. See http://releases.ubuntu.com/16.04/
2. Download all files in this repository: https://github.com/anonymous0201/ambm.git
3. Install all required packages in "INSTALL"

## Experiments
### Part I: Semantics Learning
To reproduce Part I of the experiments in the paper, run:

cd ambm_ver_0.1.0
python src/python/experiments_semantics_learning.py

Results can be found in ambm_ver_0.1.0/Experiments/semantics_learning_results/log/

### Part II: Abstract Machine Modification
To reproduce Part II of the experiments in the paper, run:

cd ambm_ver_0.1.0
python src/python/experiments_abstract_machine_modification.py

Results can be found in ambm_ver_0.1.0/Experiments/abstract_machine_modification_results/log/




