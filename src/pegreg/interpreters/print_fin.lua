local print_lr = require("pegreg.interpreters.print_lr")

----------------------------------------------------------------------------
-- A print interpreter adding fin functionality
---------------------------------------------------------------------------
local print_fin = {}

for k, v in pairs(print_lr) do
   print_fin[k] = v
end

function print_fin.fin(item)
   local out = string.format("(fin %s)", item)
   return out
end

function print_fin.notfin(item)
   -- Less cluttered. The information is still there if we need it
   local out = string.format("(notfin %s)", item)
   return out
end

return print_fin
