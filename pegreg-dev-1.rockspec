rockspec_format = "3.0"

package = "pegreg"

version = "dev-1"

source = {
   url = "*** please add URL for source tarball, zip or repository here ***"
}

description = {
   homepage = "*** please enter a project homepage ***",
   license = "*** please specify a license ***"
}

build = {
   type = "builtin",
   modules = {
      pegreg = "src/pegreg.lua",
      ["pegreg.frontends"] = "src/pegreg/frontends.lua",
      ["pegreg.frontends.fst_language"] = "src/pegreg/frontends/fst_language.lua",
      ["pegreg.frontends.language"] = "src/pegreg/frontends/language.lua",
      ["pegreg.interpreters"] = "src/pegreg/interpreters.lua",
      ["pegreg.interpreters.add_left_right"] = "src/pegreg/interpreters/add_left_right.lua",
      ["pegreg.interpreters.create_arrows"] = "src/pegreg/interpreters/create_arrows.lua",
      ["pegreg.interpreters.create_states"] = "src/pegreg/interpreters/create_states.lua",
      ["pegreg.interpreters.enumerate"] = "src/pegreg/interpreters/enumerate.lua",
      ["pegreg.interpreters.expand_ref"] = "src/pegreg/interpreters/expand_ref.lua",
      ["pegreg.interpreters.expand_string"] = "src/pegreg/interpreters/expand_string.lua",
      ["pegreg.interpreters.flatten"] = "src/pegreg/interpreters/flatten.lua",
      ["pegreg.interpreters.list_fin"] = "src/pegreg/interpreters/list_fin.lua",
      ["pegreg.interpreters.mark_fin"] = "src/pegreg/interpreters/mark_fin.lua",
      ["pegreg.interpreters.print_fin"] = "src/pegreg/interpreters/print_fin.lua",
      ["pegreg.interpreters.print_fst"] = "src/pegreg/interpreters/print_fst.lua",
      ["pegreg.interpreters.print_lr"] = "src/pegreg/interpreters/print_lr.lua",
      ["pegreg.interpreters.print_n"] = "src/pegreg/interpreters/print_n.lua",
      ["pegreg.interpreters.print_syntax"] = "src/pegreg/interpreters/print_syntax.lua",
      ["pegreg.interpreters.remark_fin"] = "src/pegreg/interpreters/remark_fin.lua",
      ["pegreg.interpreters.sc_to_cs"] = "src/pegreg/interpreters/sc_to_cs.lua",
      ["pegreg.interpreters.state_arrow"] = "src/pegreg/interpreters/state_arrow.lua",
      ["pegreg.compiler"] = "src/pegreg/compiler.lua",
      ["pegreg.compiler.nfst_to_dfst"] = "src/pegreg/compiler/nfst_to_dfst.lua",
      ["pegreg.compiler.emit_states"] = "src/pegreg/compiler/emit_states.lua",
      ["pegreg.compiler.compiler"] = "src/pegreg/compiler/compiler.lua",
      ["pegreg.data_structures"] = "src/pegreg/data_structures.lua",
      ["pegreg.data_structures.nfst"] = "src/pegreg/data_structures/nfst.lua",
      ["pegreg.data_structures.list"] = "src/pegreg/data_structures/list.lua",
      ["pegreg.algorithms"] = "src/pegreg/algorithms.lua",
      ["pegreg.algorithms.nfa_to_dfa"] = "src/pegreg/algorithms/nfa_to_dfa.lua",
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
