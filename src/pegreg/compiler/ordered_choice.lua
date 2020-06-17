-- Definitions:

-- If A is a number in the enumerated syntax tree,
-- "portion of the NFA corresponding to A" is
-- all of the states that comprise the subtree
-- of the syntax tree at A, along with
-- all of the states and arrows that can be reached
-- through these states.

-- TODO redefine this algorithm as a recursion with a base case
--      rather than a destructive operation on a DFA
-- Idea: have an interpreter subtree(N) that grabs the subtree at N
-- Algorithm orderChoices(dfa, Anfa, Bnfa, killarrows)
-- Input: DFA, the determinized version of the NFA
--        Anfa, the portion of the NFA corresponding to A in l:choice(A, B)
--        Bnfa, the portion of the NFA corresponding to B in l:choice(A, B)
--        killarrows, whether or not arrows originating only from BNFA transitions ought to be killed
-- Output: A DFA that _orders_ the choice between A and B
--         so that the DFA does not match B unless it
--         does not match A.
-- Code:
--
-- if anfa.final in dfa.root then
--   killarrows = true
-- for child of dfa.root
--   when killarrows
--     for edge in edges(dfa.root, child)
--       if edge in Anfa
--         keep edge
--   orderChoices(subgraph of dfa at child, Anfa, Bnfa, killarrows)
--
-- TODO does the order of ordering choices matter here?
--   I think it does, and I think that Anfa_lst and Bnfa_lst
--   ought to be ordered based on smallest subcomponents,
--   where there initial elements are most distant from the root
--   and the final elements are least distant from the root
-- Algorithm orderAllChoices(nfa, dfa, Anfa_lst, Bnfa_lst)
--   for Anfa, Bnfa in Anfa_lst, Bnfa_lst
--     orderChoices(nfa, dfa, Anfa, Bnfa, false)
local ordered_choice = {}

local function get_finals(state_machine)
   assert(false)
end

local function contains_substate(state_list, state_members, substate)
   assert(false)
end

local function root(state_machine)
   assert(false)
end

local function get_children(dfa)
   assert(false)
end

local function get_edges(parent, child)
   assert(false)
end

local function contains_edge(state_machine, edge)
   assert(false)
end

local function keep(dfa, edge)
   assert(false)
end

local function subgraph(state_machine, child)
   assert(false)
end

--- Order the choices between ANFA and BNFA
--- @param dfa any
--- @param state_members any
--- @param anfa any
--- @param bnfa any
--- @param killarrows boolean
function ordered_choice.order_choices(dfa, state_members, anfa, bnfa, killarrows, output)
   for final in get_finals(anfa) do
      if contains_substate(root(dfa), state_members, final) then
         killarrows = true
      end
   end
   for child in get_children(dfa) do
      for edge in get_edges(dfa.root, child) do
         if not contains_edge(anfa, edge) then
            keep(dfa, edge, output)
         end
      end
      ordered_choice.order_choices(subgraph(dfa, child), state_members, anfa, bnfa, killarrows, output)
   end
end

--- Order all of the choices
--- @param dfa any
--- The DFA produced by converting the NFA to a DFA
--- @param state_members any
--- A map from each state in the DFA to its members
--- @param anfa_lst any
--- A list of all NFAs that come on the left side of an ordered choice
--- @param bnfa_lst any
--- A list of all the NFAs that come on the right side of an ordered choice
--- @return nil
--- Delete all of the unordered parts of the dfa.
function ordered_choice.order_all_choices(dfa, state_members, anfa_lst, bnfa_lst)
   for i = 1, #anfa_lst, 1 do
      local output = {}
      ordered_choice.order_choices(dfa, state_members, anfa_lst[i], bnfa_lst[i], true, output)
      dfa = output
   end
end

return ordered_choice
