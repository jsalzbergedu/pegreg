local library = {}

local interpreters = require("pegreg.interpreters")
local frontends = require("pegreg.frontends")

for k, v in pairs(interpreters) do
   library[k] = v
end

for k, v in pairs(frontends) do
   library[k] = v
end

return library
