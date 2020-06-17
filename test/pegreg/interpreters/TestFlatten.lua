require("test.pegreg.interpreters.TestPrintFst")

local pegreg = require("pegreg")
local flatten = pegreg.flatten

TestFlatten = {}

function TestFlatten:testFlattenInterpreter()
   TestPrintFst:assertSLInterpreter(flatten)
end
