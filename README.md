# Abstract Machine Batch Modification

This repository contains the source code of the Abstract Machine Batch Modification algorithm. It is built to support the review of the paper: 
#### Automated Abstract Machine Modification Using Semantic Probabilities and Predicate Reconstitution
Due to the double-blind peer review process, authors' names are hidden.

## Section 1: Installation
1. Install Ubuntu 16.04. See http://releases.ubuntu.com/16.04/
2. Download all files in this repository: https://github.com/anonymous0201/ambm.git
3. Install all required packages in "INSTALL"

## Section 2: Experiments
### Part I: Semantics Learning
To reproduce Part I of the experiments in the paper, run:

python src/python/experiments_semantics_learning.py

Results can be found in Experiments/semantics_learning_results/log/

### Part II: Abstract Machine Modification
To reproduce Part II of the experiments in the paper, run:

python src/python/experiments_abstract_machine_modification.py

Results can be found in Experiments/abstract_machine_modification_results/log/

## Section 3: Technical Details

### Algorithm 1: Abstract Machine Batch Modification

The implementation of this algorithm is:

#### src/python/abstract_machine_batch_modification.py

#### Critical functions include:
##### "State-Diagram(M)":
This function returns the state diagram of an abstract machine M. It is a function of the ProB model checker.
 
##### "Semantics-Learning(M)":
This function is implemented as "SemLearnLib.TrainingSemanticsModel(M,conffile,sdir)". It learns the state diagram of an abstract machine M, and it returns a learnt semantics model. Semantics learning is a process that learns a binary classifier of the type T by the state diagram D. T can be BNB, LR, SVM, RF and Silas. Learning functions of scikit-learn and Silas Edu are used to train the classifier.

##### "SMT-Samples(M,N)":
This function is implemented as "SemLearnLib.MonteCarloStateSampling(M,W,conffile,mcdir)". Note that N is a parameter in the configuration file (i.e. "conffile"). It samples N states satisfying the invariants of an abstract machine M via the SMT solver of ProB. Firstly, it extracts the types of variables in M and the invariants of M. Next, the conjunction of the invariants and the types are converted to a constraint P_C. Finally, the SMT solver randomly output N solutions satisfying P_C.

#### "Faulty-Transitions(D)":
This function returns faulty transitions in a state diagram D. It is a function of the ProB model checker.

#### "Correct-States(D)":
This function returns correct states in a state diagram D. It is a function of the ProB model checker.

#### "Atomic-Modifications(T,S)":
This function synthesises atomic modifications for a set of faulty transitions T. S is a set of correct states. This function is implemented as "Bmch.RevisionSynthesis(TF,SREV)"

#### "Semantics-Probability(R,W)":
This function predicts the semantics probability of a set of transitions R via a semantics model W. It is implemented as "SemLearnLib.ScoreRevisionsUsingSemanticsModel(W,RREV,revdir)"

#### "Update(M,R)":
This function applies a set of modifications R to an abstract machine M. It is implemented as "Bmch.apply_A_change(mch,op,cond,subs)"

#### "Reconstitution(R)":
This function is Algorithm 2 - Modification Reconstitution. It is implemented as "RepSimpLib.CFGRepairSimplification(RS,TL,VList,conffile,cgfdir)"



### Algorithm 2: Modification Reconstitution

The implementation of this algorithm is:

#### "CFGRepairSimplification" in src/python/RepSimpLib.py

#### Critical functions include:
##### "Modifications-To-Predicates(M)", "CFG-Predicates(M,D)" and "Candidate-Predicates(X,P)":
The three functions are implemented as "CFG_Substitution_Generator(TL,VL,conffile,sdir)". It returns a set of candidate CFG substitutions that can describe a set of transitions. See comments in "RepSimpLib.py" for details.

##### "Best-Partition(X,W)":
This function returns a partition of a set of transitions X using a set of candidate predicates W. It is implemented as "transition_partition(TL,VL,Y)". See comments in "RepSimpLib.py" for details.

##### "Predicates-To-Modifications(X)":
This function converts a set of modification predicates X to a set of modifications. It is implemented as "convert_CFG_subs_to_str(SC[0])" and "convert_pexp_to_cond(pexp,VL)".
