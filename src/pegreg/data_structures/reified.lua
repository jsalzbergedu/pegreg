local list = require("pegreg.data_structures.list")
local reified = {}

reified.state = {}
reified.state_mt = {}
function reified.state_mt.__tostring(state)
   return string.format("(state %d %s)", state.number, state.final)
end

function reified.state_mt.__eq(state1, state2)
   return state1.number == state2.number
end

function reified.state_mt.__lt(state1, state2)
   return state1.number < state2.number
end

function reified.state_mt.__le(state1, state2)
   return state1.number <= state2.number
end

function reified.state.new(number, final)
   local state = {}
   state.number = number
   state.final = final
   setmetatable(state, reified.state_mt)
   return state
end

reified.arrow = {}
reified.arrow_mt = {}

function reified.arrow_mt.__tostring(arrow)
   local input = arrow.input
   local output = arrow.output
   if input == '' then
      input = "ε"
   end
   if output == '' then
      output = "ε"
   end
   return string.format("(arrow %d %d %s %s)",
                        arrow.from,
                        arrow.to,
                        input,
                        output)
end

function reified.arrow_mt.__eq(arrow1, arrow2)
   if arrow1.from ~= arrow2.from then
      return false
   end
   if arrow1.to ~= arrow2.to then
      return false
   end
   return true
end

function reified.arrow_mt.__lt(arrow1, arrow2)
   if arrow1.from == arrow2.from then
      return arrow1.to < arrow2.to
   end
   return arrow1.from < arrow2.from
end

function reified.arrow_mt.__le(arrow1, arrow2)
   if arrow1.from == arrow2.from then
      return arrow1.to <= arrow2.to
   end
   return arrow1.from <= arrow2.from
end

function reified.arrow.new(from, to, input, output)
   local out = {
      from = from,
      to = to,
      input = input,
      output = output
   }
   setmetatable(out, reified.arrow_mt)
   return out
end

reified.reified = {}
reified.reified_mt = {}

function reified.reified_mt.__tostring(reified)
   return string.format("(reified (states %s) (arrows %s))",
                        reified.states,
                        reified.arrows)
end

function reified.reified.new(states, arrows)
   list.assert_list(states)
   list.assert_list(arrows)
   local out = {
      states = states,
      arrows = arrows
   }
   setmetatable(out, reified.reified_mt)
   return out
end

return reified
