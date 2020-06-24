local language = require("pegreg.frontends.language")
local expand_ref = require("pegreg.interpreters.expand_ref")
local expand_string = require("pegreg.interpreters.expand_string")
local add_left_right = require("pegreg.interpreters.add_left_right")
local mark_fin = require("pegreg.interpreters.mark_fin")
local enumerate = require("pegreg.interpreters.enumerate")
local state_arrow = require("pegreg.interpreters.state_arrow")
local flatten = require("pegreg.interpreters.flatten")
local reify = require("pegreg.interpreters.reify")
local nfst_to_dfst = require("pegreg.compiler.nfst_to_dfst")
local emit_states = require("pegreg.compiler.emit_states")

local graph = require("graph")

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
      local reified = language:create(expand_ref)(expand_string)(add_left_right)(mark_fin)(enumerate)(state_arrow)(flatten)(reify)
      local g = graph.graph.new()
      local top = nfst_to_dfst.edge_list_to_graph(reified, g)
      local reachable, top_reachable, vertex_to_final = nfst_to_dfst.reachable_g(g, top)
      local dfst = nfst_to_dfst.find_dfst_from_reachable(reachable, top_reachable, vertex_to_final)
      return emit_states.from_dfst(dfst)
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
