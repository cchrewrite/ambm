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

python src/python/experiments_semantics_learning.py

Results can be found in Experiments/semantics_learning_results/log/

### Part II: Abstract Machine Modification
To reproduce Part II of the experiments in the paper, run:

python src/python/experiments_abstract_machine_modification.py

Results can be found in Experiments/abstract_machine_modification_results/log/

## Technical Details

### Algorithm 1: Abstract Machine Batch Modification

The implementation of this algorithm is:

src/python/abstract_machine_batch_modification.py

#### Critical functions include:
##### "State-Diagram(M)":
It is a function of the ProB model checker.

##### "Semantics-Learning(M)":
It is implemented as "SemLearnLib.TrainingSemanticsModel(M,conffile,sdir)"

##### "SMT-Samples(M,N)":
It is implemented as "SemLearnLib.MonteCarloStateSampling(M,W,conffile,mcdir)"

#### "Faulty-Transitions(D)":
It is a function of the ProB model checker.

#### "Correct-States(D)":
It is a function of the ProB model checker.

#### "Atomic-Modifications(T,S)":
It is implemented as "Bmch.RevisionSynthesis(TF,SREV)"

#### "Semantics-Probability(R,W)":
It is implemented as "SemLearnLib.ScoreRevisionsUsingSemanticsModel(W,RREV,revdir)"

#### "Update(M,R)":
It is implemented as "Bmch.apply_A_change(mch,op,cond,subs)"

#### "Reconstitution(R)":
It is implemented as "RepSimpLib.CFGRepairSimplification(RS,TL,VList,conffile,cgfdir)"



