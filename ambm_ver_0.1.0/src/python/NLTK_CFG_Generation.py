from nltk.parse.generate import generate, demo_grammar
from nltk import CFG
import Bmch

from RepSimpLib import *



b_subs_grammar = """
  S -> NP VP
  NP -> Det N
  PP -> P NP
  VP -> 'slept' | 'saw' NP | 'walked' PP
  Det -> 'the' | 'a'
  N -> 'man' | 'park' | 'dog'
  P -> 'in' | 'with'
"""

#b_subs_grammar = "  PRED -> '(open = TRUE)' | '(open = FALSE)' | '(move = TRUE)' | '(move = FALSE)'\n"

#subs_type = "S -> BOOL | 'bool(' PRED ')'\n"

#subs_type = "S -> INT\n"

#subs_type = "S -> PRED\n"

#subs_type = "S -> DIST1\n"

subs_type = "S -> SET1\n"

vble_types = """
  BOOL -> 'pre_open' | 'pre_move'
  INT -> 'pre_floor' | 'pre_building'
  DIST1 -> 'loc' | 'signal'
  SET1 -> 'pre_streets' | 'pre_stations'
"""

const_types = """
  INT -> '-1' | '0' | '1' | '2'
  NAT1 -> '1' | '2'
  DIST1 -> 'S0' | 'S1' | 'S2' | 'S3'
  SET1 -> '{}' | '{S0,S1}' | '{S2,S3}'
"""


common_grammar = """
  PRED -> '(' BOOL '= TRUE )'
  PRED -> '(' BOOL '= FALSE )'
  PRED -> '(' PRED '&' PRED ')'
  PRED -> '(' PRED 'or' PRED ')'
  PRED -> 'not(' PRED ')'
  PRED -> '(' INT '=' INT ')'
  PRED -> '(' INT '>=' INT ')'
  PRED -> '(' INT '<=' INT ')'

  INT -> '(' INT '+' INT ')'
  INT -> '(' INT '-' INT ')'
  INT -> '(' INT '*' INT ')'
  INT -> '(' INT '/' NAT1 ')'
  INT -> '(' INT 'mod' NAT1 ')'

"""

DS_grammar = ProduceDistAndSetCFGRules("DIST1","SET1")

b_subs_grammar = subs_type + vble_types const_types + common_grammar + DS_grammar

grammar = CFG.fromstring(b_subs_grammar)

print(grammar)

#for sentence in generate(grammar, n=10):
#    print(' '.join(sentence))


X = []
for sentence in generate(grammar, depth=5):
    S = ' '.join(sentence)
    print S
    X.append(S)
print len(X)

