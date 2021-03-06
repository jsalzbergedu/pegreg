local algorithms = {}

algorithms.nfa_to_dfa = require("pegreg.algorithms.nfa_to_dfa")
algorithms.dominators = require("pegreg.algorithms.dominators")
algorithms.demote = require("pegreg.algorithms.demote")

return algorithms
