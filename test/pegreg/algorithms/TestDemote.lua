require("test.pegreg.algorithms.TestNFAToDFA")

local luaunit = require("luaunit")
local pegreg = require("pegreg")
local nfa_to_dfa = pegreg.nfa_to_dfa
local dominators = pegreg.dominators
local demote = pegreg.demote

--- Tests for demoting unreachable states
--- @global TestDemote
TestDemote = {}

function TestDemote:abstract_from_nfa(abstract)
   local impl = {}

   function impl:opposite(node, edge)
      if node == edge:from() then
         return edge:to()
      end
      return edge:from()
   end

   function impl:incoming_edges(node)
      local arrow_list = {}
      for arrow in abstract:arrows() do
         if arrow:to() == node then
            table.insert(arrow_list, arrow)
         end
      end
      table.sort(arrow_list, function (a, b)
                               return a:from():number() < b:from():number()
                             end)
      local idx = 1
      local function it()
         if idx > #arrow_list then
            return nil
         end
         local out = arrow_list[idx]
         idx = idx + 1
         return out
      end
      return it
   end

   function impl:contains(node)
      for state in abstract:states() do
         if node == state then
            return true
         end
      end
      return false
   end

   function impl:children(node)
      local children = {}
      for arrow in abstract:arrows() do
         if arrow:from() == node then
            table.insert(children, arrow:to())
         end
      end
      table.sort(children, function (a, b) return a:number() < b:number() end)
      local idx = 1
      local function it()
         if idx > #children then
            return nil
         end
         local out = children[idx]
         idx = idx + 1
         return out
      end
      return it
   end

   function impl:edges()
      return abstract:arrows()
   end

   function impl:verticies()
      return abstract:states()
   end

   local abstract_impl = getmetatable(abstract)
   setmetatable(impl, {__index = abstract_impl.__index})
   return setmetatable(abstract, {__index = impl})
end

-- Tests
-- (A/B) K
-- (a/aa)b
function TestDemote:testAOrderedChoiceAAB()
   local q0 = 0
   local a0 = 1
   local af = 2
   local kf = 3
   local b0 = 4
   local b1 = 5
   local bf = 6
   local arrows = {
      {
         {q0, false},
         {a0, false},
         {af, false},
         {kf, true},
         {b0, false},
         {b1, false},
         {bf, false}
      },
      {
         {q0, a0, ''},
         {q0, b0, ''},
         {a0, af, 'a'},
         {b0, b1, 'a'},
         {b1, bf, 'a'},
         {af, kf, 'b'},
         {bf, kf, 'b'}
      }
   }
   local nfa = TestNFAToDFA:abstract_from_basic(arrows)
   local dfa = nfa_to_dfa.decorate(nfa_to_dfa.determinize(nfa))
   local demotable = TestDemote:abstract_from_nfa(dfa)

   local expected_demotable = {
      {
         {{q0, false}, {a0,false}, {b0, false}},
         {{af, false}, {b1, false}},
         {{bf, false}},
         {{kf, true}},
      },
      {
         {0, 1, "a"},
         {1, 2, "a"},
         {1, 3, "b"},
         {2, 3, "b"},
      }
   }
   luaunit.assertEquals(demotable, expected_demotable)
   local idom = dominators.dominators(demotable, demotable:start())

   local af_state = nfa[1][af + 1]

   luaunit.assertFalse(demote.dfa_dominated(idom, dfa, dfa[1][1], af_state))
   luaunit.assertTrue(demote.dfa_dominated(idom, dfa, dfa[1][2], af_state))
   luaunit.assertTrue(demote.dfa_dominated(idom, dfa, dfa[1][3], af_state))
   luaunit.assertTrue(demote.dfa_dominated(idom, dfa, dfa[1][4], af_state))

   local b1_state = nfa[1][b1 + 1]
   local bf_state = nfa[1][bf + 1]
   local bstates = {b1_state, bf_state}

   luaunit.assertEquals(demote.dfa_demotable(idom, dfa, dfa[1][1], af_state, bstates),
                        {})
   luaunit.assertEquals(demote.dfa_demotable(idom, dfa, dfa[1][2], af_state, bstates),
                        {b1_state})
   luaunit.assertEquals(demote.dfa_demotable(idom, dfa, dfa[1][3], af_state, bstates),
                        {bf_state})
   luaunit.assertEquals(demote.dfa_demotable(idom, dfa, dfa[1][4], af_state, bstates),
                        {})

   return demotable, idom
end

-- (A*) K
--  a*  a
function TestDemote:testAStarA()
   local q0 = 0
   local a0 = 1
   local af = 2
   local k0 = 3
   local kf = 4

   local arrows = {
      {
         {q0, false},
         {a0, false},
         {af, false},
         {k0, false},
         {kf, true}
      },
      {
         {q0, a0, ''},
         {a0, af, 'a'},
         {af, q0, ''},
         {q0, k0, ''},
         {k0, kf, 'a'}
      }
   }

   local nfa = TestNFAToDFA:abstract_from_basic(arrows)
   local dfa = nfa_to_dfa.decorate(nfa_to_dfa.determinize(nfa))
   local demotable = TestDemote:abstract_from_nfa(dfa)
   local expected_demotable = {
      {
         {{q0, false}, {a0, false}, {k0, false}},
         {{q0, false}, {a0, false}, {af, false}, {k0, false}, {kf, true}}
      },
      {
         {0, 1, "a"},
         {1, 1, "a"}
      }
   }
   luaunit.assertEquals(demotable, expected_demotable)
   local idom = dominators.dominators(demotable, demotable:start())
   local af_state = arrows[1][af + 1]
   local kf_state = nfa[1][kf + 1]
   local kstates = {kf_state}
   luaunit.assertEquals(demote.dfa_demotable(idom, dfa, dfa[1][1], af_state, kstates),
                        {})
   luaunit.assertEquals(demote.dfa_demotable(idom, dfa, dfa[1][2], af_state, kstates),
                        {kf_state})

end
