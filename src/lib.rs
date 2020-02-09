pub use mmb_types::opcode;

#[derive(Copy, Clone)]
enum Ptr {
    Ref { id: u32 },
    Term { id: u32 },
}

#[derive(Debug, Copy, Clone)]
pub enum ConversionError {
    InvalidTermIndex,
}

#[derive(Copy, Clone)]
struct HeapAlloc(Ptr);

#[derive(Debug, Copy, Clone)]
enum Cmd {
    Ref { id: u32 },
    Term { id: u32 },
    TermSave { id: u32 },
    Dummy { sort: u32 },
    Hyp,
}

struct Term {
    id: u32,
    nr_args: u32,
    ptr_args: usize,
}

fn term(
    id: u32,
    nr_args: u32,
    data: &mut Vec<Term>,
    args: &mut Vec<Ptr>,
    stack: &mut Vec<Ptr>,
) -> Ptr {
    let ptr_args = args.len();
    let ptr = data.len();

    data.push(Term {
        id,
        nr_args,
        ptr_args,
    });

    let len = stack.len();
    let diff = len - nr_args as usize;
    let last_elements = stack.get(diff..).unwrap();

    args.extend(last_elements);

    stack.truncate(diff);

    Ptr::Term { id: ptr as u32 }
}

pub fn unify_to_proof<'a, T, F>(
    init_vars: u32,
    unify_stream: T,
    get_nr_args: F,
) -> Result<Vec<opcode::Command<opcode::Proof>>, ConversionError>
where
    T: IntoIterator<Item = &'a opcode::Command<opcode::Unify>>,
    F: Fn(u32) -> Option<u32>,
{
    let mut command_stack = Vec::new();
    let mut counter = init_vars;

    for command in unify_stream {
        use opcode::Unify;
        match command.opcode {
            Unify::TermSave => {
                counter += 1;
            }
            Unify::Dummy => {
                counter += 1;
            }
            Unify::End => {
                break;
            }
            _ => {}
        }

        command_stack.push(command);
    }

    let mut data = Vec::new();
    let mut args: Vec<Ptr> = Vec::new();
    let mut stack = Vec::new();
    let mut heap_translate = Vec::new();

    let mut buffer = Vec::new();

    while let Some(command) = command_stack.pop() {
        use opcode::Unify;
        match command.opcode {
            Unify::End => {
                //
            }
            Unify::Ref => {
                stack.push(Ptr::Ref {
                    id: command.operand,
                });
            }
            Unify::Term => {
                let nr_args =
                    get_nr_args(command.operand).ok_or(ConversionError::InvalidTermIndex)?;
                let ret = term(command.operand, nr_args, &mut data, &mut args, &mut stack);

                stack.push(ret);
            }
            Unify::TermSave => {
                let nr_args =
                    get_nr_args(command.operand).ok_or(ConversionError::InvalidTermIndex)?;
                let ret = term(command.operand, nr_args, &mut data, &mut args, &mut stack);

                let ref_var = counter;
                counter -= 1;

                stack.push(Ptr::Ref { id: ref_var });
                heap_translate.push((ref_var, HeapAlloc(ret)));
            }
            Unify::Dummy => {
                let ref_var = counter;
                counter -= 1;

                let ret = Ptr::Ref {
                    id: command.operand,
                };

                stack.push(Ptr::Ref { id: ref_var });
                heap_translate.push((ref_var, HeapAlloc(ret)));
            }
            Unify::Hyp => {
                expand_preorder(stack.iter(), &mut buffer, &data, &args);
                stack.clear();
                buffer.push(Cmd::Hyp);
            }
        }
    }

    expand_preorder(stack.iter(), &mut buffer, &data, &args);
    stack.clear();

    let mut temp = Vec::new();

    for i in buffer {
        let translate = heap_translate.last();

        match (i, translate) {
            (Cmd::Ref { id }, Some((trans_id, HeapAlloc(value)))) => {
                if id == *trans_id {
                    match value {
                        Ptr::Ref { id } => temp.push(Cmd::Dummy { sort: *id }),
                        Ptr::Term { id } => {
                            let term = data.get(*id as usize).unwrap();
                            let ptrs = args
                                .get(term.ptr_args..(term.ptr_args + term.nr_args as usize))
                                .unwrap();

                            expand_preorder(ptrs.iter().rev(), &mut temp, &data, &args);

                            temp.push(Cmd::TermSave { id: term.id });
                        }
                    }

                    heap_translate.pop();
                } else {
                    temp.push(i);
                }
            }
            _ => {
                temp.push(i);
            }
        }
    }

    let done = temp
        .into_iter()
        .map(|c| match c {
            Cmd::Ref { id } => opcode::Command {
                opcode: opcode::Proof::Ref,
                operand: id,
            },
            Cmd::Term { id } => opcode::Command {
                opcode: opcode::Proof::Term,
                operand: id,
            },
            Cmd::TermSave { id } => opcode::Command {
                opcode: opcode::Proof::TermSave,
                operand: id,
            },
            Cmd::Dummy { sort } => opcode::Command {
                opcode: opcode::Proof::Dummy,
                operand: sort,
            },
            Cmd::Hyp => opcode::Command {
                opcode: opcode::Proof::Hyp,
                operand: 0,
            },
        })
        .collect();

    Ok(done)
}

fn expand_preorder<'a, I>(ptrs: I, out: &mut Vec<Cmd>, data: &[Term], args: &[Ptr])
where
    I: Iterator<Item = &'a Ptr>,
{
    for i in ptrs {
        match i {
            Ptr::Ref { id } => out.push(Cmd::Ref { id: *id }),
            Ptr::Term { id } => {
                let term = data.get(*id as usize).unwrap();
                let ptrs = args
                    .get(term.ptr_args..(term.ptr_args + term.nr_args as usize))
                    .unwrap();

                expand_preorder(ptrs.iter().rev(), out, data, args);

                out.push(Cmd::Term { id: term.id });
            }
        }
    }
}
