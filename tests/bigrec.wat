(module
  (func (export "idrec") (param i32) (result i32)
    local.get 0
    if (result i32)
         local.get 0
         i32.const 1
         i32.sub
         call 0
         i32.const 1
         i32.add
    else i32.const 0
    end
)
  (func (export "main") (result i32)
    i32.const 1048576
    call 0
  )
)
