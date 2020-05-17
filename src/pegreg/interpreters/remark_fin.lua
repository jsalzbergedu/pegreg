local mark_fin = require("pegreg.interpreters.mark_fin")
local enumerate = require("pegreg.interpreters.enumerate")

--------------------------------------------------------------------------------
-- An interpreter that remarks final states
--------------------------------------------------------------------------------
local remark_fin = {}
for k, v in pairs(mark_fin) do
   remark_fin[k] = v
end

function remark_fin.mark_n(n, item)
   return function (t, i)
      return i.mark_n(n, item(t, i))
   end
end

function remark_fin.fin(item)
   return item
end

function remark_fin.notfin(item)
   return item
end

return remark_fin
