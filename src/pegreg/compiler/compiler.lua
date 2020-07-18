local language = require("pegreg.frontends.language")
local reify = require("pegreg.interpreters.reify")
local expand_ref = require("pegreg.interpreters.expand_ref")
local expand_string = require("pegreg.interpreters.expand_string")
local add_left_right = require("pegreg.interpreters.add_left_right")
local mark_fin = require("pegreg.interpreters.mark_fin")
local enumerate = require("pegreg.interpreters.enumerate")
local state_arrow = require("pegreg.interpreters.state_arrow")
local flatten = require("pegreg.interpreters.flatten")
local nfa_to_dfa = require("pegreg.algorithms.nfa_to_dfa")
local emit_states = require("pegreg.compiler.emit_states")

local compiler = {}

function compiler.l()
   local language = language.l()
   local l = {}

   function l:rule(name)
      local rule = {}
      function rule:is(tobind)
         language:rule(name):is(tobind)
         return l
      end
      return rule
   end

   function l:grammar(item)
      language:grammar(item)
      return l
   end

   function l:create()
      local nfa = language:create(expand_ref)(expand_string)(add_left_right)(mark_fin)(enumerate)(state_arrow)(flatten)(reify)
      local dfa = nfa_to_dfa.decorate(nfa_to_dfa.determinize(nfa))
      return emit_states.from_abstract(dfa)
   end

   function l:lit(str)
      return language:lit(str)
   end

   function l:seq(rule1, rule2)
      return language:seq(rule1, rule2)
   end

   function l:choice(rule1, rule2)
      return language:choice(rule1, rule2)
   end

   function l:ref(rule)
      return language:ref(rule)
   end

   function l:star(item)
      return language:star(item)
   end

   function l:e()
      return language:e()
   end

   return l
end

return compiler
