local interpreters = {}

interpreters.add_left_right = require("pegreg.interpreters.add_left_right")
interpreters.create_arrows = require("pegreg.interpreters.create_arrows")
interpreters.create_states = require("pegreg.interpreters.create_states")
interpreters.enumerate = require("pegreg.interpreters.enumerate")
interpreters.expand_ref = require("pegreg.interpreters.expand_ref")
interpreters.expand_string = require("pegreg.interpreters.expand_string")
interpreters.flatten = require("pegreg.interpreters.flatten")
interpreters.list_fin = require("pegreg.interpreters.list_fin")
interpreters.mark_fin = require("pegreg.interpreters.mark_fin")
interpreters.print_fin = require("pegreg.interpreters.print_fin")
interpreters.print_nfa = require("pegreg.interpreters.print_nfa")
interpreters.print_lr = require("pegreg.interpreters.print_lr")
interpreters.print_n = require("pegreg.interpreters.print_n")
interpreters.print_syntax = require("pegreg.interpreters.print_syntax")
interpreters.remark_fin = require("pegreg.interpreters.remark_fin")
interpreters.sc_to_cs = require("pegreg.interpreters.sc_to_cs")
interpreters.state_arrow = require("pegreg.interpreters.state_arrow")
interpreters.reify = require("pegreg.interpreters.reify")

return interpreters
