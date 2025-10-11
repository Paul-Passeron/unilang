use inkwell::context::Context;

pub mod mono_ir_pass;

pub fn test() {
    let context = Context::create();
    let module = context.create_module("addition");
    let i32_type = context.i32_type();

    let fn_type = i32_type.fn_type(&[i32_type.into(), i32_type.into()], false);
    let fn_val = module.add_function("add", fn_type, None);
    let entry_basic_block = context.append_basic_block(fn_val, "entry");

    let builder = context.create_builder();
    builder.position_at_end(entry_basic_block);

    let x = fn_val.get_nth_param(0).unwrap().into_int_value();
    let y = fn_val.get_nth_param(1).unwrap().into_int_value();

    let ret = builder.build_int_add(x, y, "add").unwrap();
    builder.build_return(Some(&ret)).unwrap();

    println!("{}", module.print_to_string().to_string());
}
