rockspec_format = "3.0"
package = "pegreg"
version = "dev-1"
source = {
   url = "git+https://github.com/jsalzbergedu/pegreg.git"
}
description = {
   summary = "# PEGREG A lua library for compiling a subset of PEGs to FSTs.",
   detailed = [[
# PEGREG
A lua library for compiling a subset of PEGs to FSTs.
Requires fst-fast-system (an NFST interpreter) and fst-fast (a lua library wrapping fst-fast-system).
]],
   homepage = "https://github.com/jsalzbergedu/pegreg",
   license = "*** please specify a license ***"
}
build = {
   type = "builtin",
   modules = {
      ["pegreg.algorithms.demote"] = "src/pegreg/algorithms/demote.lua",
      ["pegreg.algorithms.dominators"] = "src/pegreg/algorithms/dominators.lua",
      ["pegreg.algorithms"] = "src/pegreg/algorithms/init.lua",
      ["pegreg.algorithms.nfa_to_dfa"] = "src/pegreg/algorithms/nfa_to_dfa.lua",
      ["pegreg.api.graph"] = "src/pegreg/api/graph.lua",
      ["pegreg.api.nfa"] = "src/pegreg/api/nfa.lua",
      ["pegreg.compiler.compiler"] = "src/pegreg/compiler/compiler.lua",
      ["pegreg.compiler.emit_states"] = "src/pegreg/compiler/emit_states.lua",
      ["pegreg.compiler"] = "src/pegreg/compiler/init.lua",
      ["pegreg.frontends.fst_language"] = "src/pegreg/frontends/fst_language.lua",
      ["pegreg.frontends"] = "src/pegreg/frontends/init.lua",
      ["pegreg.frontends.language"] = "src/pegreg/frontends/language.lua",
      ["pegreg"] = "src/pegreg/init.lua",
      ["pegreg.interpreters.add_left_right"] = "src/pegreg/interpreters/add_left_right.lua",
      ["pegreg.interpreters.create_arrows"] = "src/pegreg/interpreters/create_arrows.lua",
      ["pegreg.interpreters.create_states"] = "src/pegreg/interpreters/create_states.lua",
      ["pegreg.interpreters.enumerate"] = "src/pegreg/interpreters/enumerate.lua",
      ["pegreg.interpreters.expand_ref"] = "src/pegreg/interpreters/expand_ref.lua",
      ["pegreg.interpreters.expand_string"] = "src/pegreg/interpreters/expand_string.lua",
      ["pegreg.interpreters.flatten"] = "src/pegreg/interpreters/flatten.lua",
      ["pegreg.interpreters"] = "src/pegreg/interpreters/init.lua",
      ["pegreg.interpreters.list_fin"] = "src/pegreg/interpreters/list_fin.lua",
      ["pegreg.interpreters.mark_fin"] = "src/pegreg/interpreters/mark_fin.lua",
      ["pegreg.interpreters.print_fin"] = "src/pegreg/interpreters/print_fin.lua",
      ["pegreg.interpreters.print_fst"] = "src/pegreg/interpreters/print_fst.lua",
      ["pegreg.interpreters.print_lr"] = "src/pegreg/interpreters/print_lr.lua",
      ["pegreg.interpreters.print_n"] = "src/pegreg/interpreters/print_n.lua",
      ["pegreg.interpreters.print_syntax"] = "src/pegreg/interpreters/print_syntax.lua",
      ["pegreg.interpreters.reify"] = "src/pegreg/interpreters/reify.lua",
      ["pegreg.interpreters.remark_fin"] = "src/pegreg/interpreters/remark_fin.lua",
      ["pegreg.interpreters.sc_to_cs"] = "src/pegreg/interpreters/sc_to_cs.lua",
      ["pegreg.interpreters.state_arrow"] = "src/pegreg/interpreters/state_arrow.lua",
      ["pegreg.util.array"] = "src/pegreg/util/array.lua",
      ["pegreg.util"] = "src/pegreg/util/init.lua"
   }
}

test_dependencies = {
   "luaunit >= 3",
   "luafilesystem >= 1.8",
}

dependencies = {

}

test = {
   type = "command",
   script = "test.lua"
}
