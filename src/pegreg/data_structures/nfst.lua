local list = require("pegreg.data_structures.list")
local nfst = {}

nfst.state = {}
nfst.state_mt = {}
function nfst.state_mt.__tostring(state)
   return string.format("(state %d %s)", state.number, state.final)
end

function nfst.state_mt.__eq(state1, state2)
   return state1.number == state2.number
end

function nfst.state_mt.__lt(state1, state2)
   return state1.number < state2.number
end

function nfst.state_mt.__le(state1, state2)
   return state1.number <= state2.number
end

function nfst.state.new(number, final)
   local state = {}
   state.number = number
   state.final = final
   setmetatable(state, nfst.state_mt)
   return state
end

function nfst.assert_state(state)
   assert(getmetatable(state) == nfst.state_mt)
end

nfst.arrow = {}
nfst.arrow_mt = {}

function nfst.arrow_mt.__tostring(arrow)
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

function nfst.arrow_mt.__eq(arrow1, arrow2)
   if arrow1.from ~= arrow2.from then
      return false
   end
   if arrow1.to ~= arrow2.to then
      return false
   end
   return true
end

function nfst.arrow_mt.__lt(arrow1, arrow2)
   if arrow1.from == arrow2.from then
      return arrow1.to < arrow2.to
   end
   return arrow1.from < arrow2.from
end

function nfst.arrow_mt.__le(arrow1, arrow2)
   if arrow1.from == arrow2.from then
      return arrow1.to <= arrow2.to
   end
   return arrow1.from <= arrow2.from
end

function nfst.arrow.new(from, to, input, output)
   local out = {
      from = from,
      to = to,
      input = input,
      output = output
   }
   setmetatable(out, nfst.arrow_mt)
   return out
end

function nfst.assert_arrow(arrow)
   assert(getmetatable(arrow) == nfst.arrow_mt)
end

nfst.nfst = {}
nfst.nfst_mt = {}

function nfst.nfst_mt.__tostring(reified)
   return string.format("(reified (states %s) (arrows %s))",
                        reified.states,
                        reified.arrows)
end

function nfst.nfst.new(states, arrows)
   list.assert_list(states)
   list.assert_list(arrows)
   for _, v in ipairs(states) do
      nfst.assert_state(v)
   end
   for _, v in ipairs(arrows) do
      nfst.assert_arrow(v)
   end

   local out = {
      states = states,
      arrows = arrows
   }
   setmetatable(out, nfst.nfst_mt)
   return out
end

return nfst
