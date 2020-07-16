local compiler = {}

compiler.nfst_to_dfst = require("pegreg.compiler.nfst_to_dfst")
compiler.emit_states = require("pegreg.compiler.emit_states")
compiler.compiler = require("pegreg.compiler.compiler")
compiler.ordered_choice = require("pegreg.compiler.ordered_choice")

return compiler