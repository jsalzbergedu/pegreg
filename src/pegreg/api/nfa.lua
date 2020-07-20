--------------------------------------------------------------------------------
-- Type signatures for an NFA.
-- These type signatures can be used to enhance IDE completion
-- for IDEs implementing EmmyLua types,
-- and can be used as a reference
--
-- NFA expected interface:
-- Base types: State, Arrow
-- Composite type: NFA
-- State has the following methods
--   state:number() get the states number
--   state:final() get whether the state is final
--   state:contains(substate) return whether the state contains the substate
--   state:substates() return an iterator over the substates of the state
-- Arrow has the following methods
--   arrow:from() gets the State that it is from
--   arrow:to() gets the State that it is to
--   arrow:input() gets the input character
-- NFA has the following methods
--   nfa:outgoing(state)
--     get all of the outgoing arrows of the
--     nfa at state.
--   nfa:states()
--     get all the states as an iterator over States
--   nfa:size()
--     get the number of states in the nfa
--   nfa:arrows()
--     get all the arrows as an iterator over Arrows
--   nfa:start()
--     get the start state of the nfa
--------------------------------------------------------------------------------
--- State of an NFA or DFA.
--- May contain substates.
--- @class State
local state = {}

--- Get the number from the state.
--- @return number number the number of the state
function state:number()
   error("unimplemented")
end

--- Get whether the state is final.
--- @return boolean final whether the state is final
function state:final()
   error("unimplemented")
end

--- Get whether the state contains the substate
--- @param substate State the state that may be a part of self
--- @return boolean contained whether the substate is contained in self
function state:contains(substate)
   error(tostring(substate) .. "unimplemented")
end

--- Return an iterator over the substates
--- @return fun():State iterator a function over the states
function state:substates()
end

--- Arrow of an NFA or DFA
--- @class Arrow
local arrow = {}

--- Get the state the arrow is from
--- @return State from
function arrow:from()
end

--- Get the state the arrow is to
--- @return State to
function arrow:to()
end

--- Get the input character for the arrow
--- @return string input
function arrow:input()
end

--- An NFA. States may contain substates
--- @class NFA
local nfa = {}

--- Get all outgoing states of the nfa at state
--- @param state State the state
--- @return fun(): State iterator over the outgoing states
function nfa:outgoing(state)
   error(tostring(state) .. "unimplemented")
end

--- Get an iterator over all of the states
--- of the nfa
--- @return fun(): State iterator over all states
function nfa:states()
end

--- Get an iterator over all arrows of the nfa
--- @return fun(): Arrow iterator over all states
function nfa:arrows()
end

--- Get the start state of the nfa
--- @return State start the start state
function nfa:start()
end

--- Get the size of the nfa
--- @return number size the size of the nfa
function nfa:size()
end

return nfa, arrow, state
