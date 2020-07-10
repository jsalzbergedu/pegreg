local luaunit = require("luaunit")
local pegreg = require("pegreg")
local reify = pegreg.reify
local emit_states = pegreg.emit_states
local ordered_choice = pegreg.ordered_choice
local nfst_to_dfst = pegreg.nfst_to_dfst

TestOrderedChoice = {}

local function reify_fromtestdata(testdata)
   local state_source = testdata[1]
   local arrow_source = testdata[2]
   local reified_states = {}
   for _, v in ipairs(state_source) do
      local number = v[1]
      local final = v[2]
      table.insert(reified_states, reify.state(number, final))
   end

   local reified_arrows = {}
   for _, v in ipairs(arrow_source) do
      local from = v[1]
      local to = v[2]
      local input = v[3]
      local output = v[4]
      table.insert(reified_arrows, reify.arrow(from, to, input, output))
   end

   local paired_states = reify.null()
   for _, v in ipairs(reified_states) do
      paired_states = reify.pair(v, paired_states)
   end

   local paired_arrows = reify.null()
   for _, v in ipairs(reified_arrows) do
      paired_arrows = reify.pair(v, paired_arrows)
   end

   return reify.create(paired_states, paired_arrows)
end

--- Test (a/aa)b
--- AKA, (A/B)K
--- For starters, if this were unordered choice,
--- we would have (a|aa)b and the language would comprise {"ab", "aab"}.
--- However, since this is posessive, ordered choice,
--- once that singular 'a' is matched it can never
--- be given up, limiting the language to {"ab"}
---
--- To implement this, we remove all parts of the DFST
--- that are reached via transitions in the B state
--- of (A/B)K after a final state of A has been reached.
--- So while (a|aa)b would become
--- states: {q0, A0, AF, KA, B0, B1, BF, KB}
--- arrows (from, to, character):
--- 0: q0, A0, ε
--- 1: A0, AF, 'a'
--- 2: AF, KA, 'b'
--- 3: q0, B0, ε
--- 4: B0, B1, 'a'
--- 5: B1, BF, 'a'
--- 6: BF, KB, 'b'
---
--- where 1 through 2 would be called the transitions corresponding to A
--- corresponding to A
--- and 4 through 6 would be called the transitions corresponding to B
---
--- And the DFA would be
--- states: {{q0, A0, B0}, {AF, B1}, {KA}, {BF}, {KB}}
--- arrows:
--- 0: {q0, A0, B0}, {AF, B1}, 'a'
--- 1: {AF, B1}, {KA}, 'b'
--- 2: {AF, B1}, {BF}, 'a'
--- 3: {BF}, {KB}, 'b'
---
--- The removal algorithm will flag
--- transition 2 as neccessary to delete,
--- TODO transition 2 or BF (?)
--- because it comes from B's nfa exclusively
--- and occurs after the final A state has already
--- been reached.
--- Thus we will end up with the DFA:
--- states: {{q0, A0, B0}, {AF, B1}, {KA}}
--- Arrows:
--- 0: {q0, A0, B0}, {AF, B1}, 'a'
--- 1: {AF, B1}, {KA}, 'b'
--- Which has the same semantics as PEG's ordered choice.
function TestOrderedChoice:testOrderChoices()
   --- We need
   --- the ANFA,
   --- The BNFA,
   --- The DFA,
   --- and killarrows is false.

   --- Including 3 in arrows
   --- even though 3 is not part of
   --- ANFA. Really, whats important
   --- is where ANFA ends
   --- and what transitions out of it exist
   local anfa_source = {
      {{2, true}, {1, false}},
      {{1, 2, 'a', 'a'}}
   }
   local anfa = reify_fromtestdata(anfa_source)

   local bnfa_source = {
      {{6, true}, {5, false}, {4, false}},
      {{4, 5, 'a', 'a'}, {5, 6, 'a', 'a'}, {6, 7, 'b', 'b'}}
   }
   local bnfa = reify_fromtestdata(bnfa_source)

   local dfa_source = {
      {{4, true}, {3, false}, {2, true}, {1, false}, {0, false}},
      {{0, 1, 'a', 'a'}, {1, 2, 'b', 'b'}, {1, 3, 'a', 'a'}, {3, 4, 'b', 'b'}}
   }
   local dfa = reify_fromtestdata(dfa_source)

   -- Now lets test that this DFA can indeed match "ab" and "aab"
   do
      local it = emit_states.from_dfst(dfa)
      do
         local outstr, match_success, matched_states = it:match_string("ab")
         luaunit.assertEquals(outstr, "ab")
         luaunit.assertTrue(match_success)
         luaunit.assertEquals(matched_states, {1, 2})
      end

      do
         local outstr, match_success, matched_states = it:match_string("aab")
         luaunit.assertEquals(outstr, "aab")
         luaunit.assertTrue(match_success)
         luaunit.assertEquals(matched_states, {1, 3, 4})
      end
   end

   -- Table from a state to its members
   local state_members = {}
   -- {q0, A0, B0}
   state_members[0] = {0, 1, 4}
   -- {AF, B1}
   state_members[1] = {2, 5}
   -- {KA}
   state_members[2] = {3}
   -- {BF}
   state_members[3] = {6}
   -- {KB}
   state_members[4] = {7}

   -- The expected output
   -- states: {{q0, A0, B0}, {AF, B1}, {KA}}
   -- Arrows:
   -- 0: {q0, A0, B0}, {AF, B1}, 'a'
   -- 1: {AF, B1}, {KA}, 'b'
   local expected_dfa_source = {
      {{2, true}, {1, false}, {0, false}},
      {{0, 1, 'a', 'a'}, {1, 2, 'b', 'b'}}
   }
   local expected_dfa = reify_fromtestdata(expected_dfa_source)
   -- Check that this is possessive
   do
      local it = emit_states.from_dfst(expected_dfa)
      do
         local outstr, match_success, matched_states = it:match_string("ab")
         luaunit.assertEquals(outstr, "ab")
         luaunit.assertTrue(match_success)
         luaunit.assertEquals(matched_states, {1, 2})
      end
      do
         local outstr, match_success, matched_states = it:match_string("aab")
         luaunit.assertEquals(outstr, "a")
         luaunit.assertFalse(match_success)
         luaunit.assertEquals(matched_states, {1, 3, 3})
      end
   end

   local output = {}
   ordered_choice.order_choices(dfa, state_members, anfa, bnfa, false, output)
   local output_sorted = nfst_to_dfst.nub(output[1])
   local expected_dfa_sorted = nfst_to_dfst.nub(expected_dfa)
   luaunit.assertEquals(output_sorted, expected_dfa_sorted)
end
