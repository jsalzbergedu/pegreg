local print_fin = require("pegreg.interpreters.print_fin")

----------------------------------------------------------------------------
-- A print interpreter that adds mark_n functionality
---------------------------------------------------------------------------
local print_n = {}

for k, v in pairs(print_fin) do
   print_n[k] = v
end

function print_n.mark_n(n, item)
   local out = string.format("(# %d %s)", n, item)
   return out
end

return print_n
