local dominators = require("pegreg.algorithms.dominators")

--------------------------------------------------------------------------------
-- A set of algorithms that finds demoted states.
-- A demoted state is a state that would exist
-- in regular languages, but cannot exist in the
-- DFAs of a PEGREG because they
-- contain parts of a possesive expression that successfully
-- matched.
-- The following terminology will be used throughought
-- the implementation of this algorithm:
--
-- A, B, K: Arbitrary PEGREGS
-- (A*)K: possessive repitition of A followed by K
-- (A/B)K: ordered choice between A and B followed by K
-- nfa(X): the NFA corresponding to the regular expression X
-- A_F, B_F, K_F: Final states of A, B, and K in the NFAs
--                of their expressions
--                (EG. A_F would be in both nfa((A/B)K) and nfa(A*K))
-- dfa(nfa(X)): the DFA corrresponding to nfa(X) (powerset construction)
-- A states, B states, K states: The states corresponding to
--                               the state machines of nfa(A),
--                               nfa(B), and nfa(K) respectively,
--                               and their substates in the combined
--                               DFA representation of each
-- In the case of
-- (A*)K, the demoted states are all K_F states
--        that are dominated by A_F.
-- In the case of (A/B)K, translated to (AK_A/BK_B),
-- the demoted states are all B states and K_B states
-- that are dominated by A_F.
-- Because the definition of a B state comes from higher up
-- in the compiler chain (in AST expansion, under
-- sc to cs and under the "choice" and "star")
--
-- This module will require a DFA that corresponds to the following interface:
-- dfa:states():
--  returns a list of STATEs
-- The DFA must also implement the graph interface
--   specified by dominators.lua.
--
-- each STATE must implement the following
-- state:contains(NFASTATE)
--  where the NFA state is an arbitrary state in the NFA corresponding
--  to the DFA
--
-- TODO: After further consideration,
-- I had to revisit my definition yet again.
-- Start states dominated by A_F should not be removed.
-- This is because possessiveness comes from simulating an
-- NFA where passing through A_F causes K or B to fail;
-- however, K0 or B0 do not represent states _inside_ the K and B
-- machines and thus need not fail.
--------------------------------------------------------------------------------
local demote = {}

--------------------------------------------------------------------------------
-- First query: given an IDOM,
-- is the state X is dominated by A_F?
-- To answer this, find all DFA states
-- that contain A_F.
-- Then, check if X is dominated by any of these states.
--------------------------------------------------------------------------------
function demote.dfa_dominated(idom, dfa, x, af)
   local afs = {}
   for state in dfa:states() do
      if state:contains(af) then
         table.insert(afs, state)
      end
   end
   for _, dominator in ipairs(afs) do
      if dominators.dominated_by(idom, x, dominator) then
         return true
      end
   end
   return false
end

--------------------------------------------------------------------------------
-- Second query:
-- Given IDOM,
-- which states in X are demotable (k or b dominated by A_F) state?
-- To answer this, we need an array of BSTATES.
-- If the BSTATES are dominated by A_F, then we can demote them.
-- Return an array of demotable substates
--------------------------------------------------------------------------------
function demote.dfa_demotable(idom, dfa, x, af, bstates)
   local demotable = {}

   if demote.dfa_dominated(idom, dfa, x, af) then
      for _, state in ipairs(bstates) do
         if x:contains(state) and state:number() > 0 then
            table.insert(demotable, state)
         end
      end
   end

   return demotable
end

return demote
