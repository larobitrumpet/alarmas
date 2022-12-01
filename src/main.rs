// alarmas

/* MIT License

Copyright (c) 2022 Lucy Robillard

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE. */

use std::env;
use std::process;
use std::fs::File;
use std::io::{self, BufRead, prelude::*};
use std::path::Path;
use std::collections::HashMap;
use std::num::IntErrorKind::PosOverflow;
use hex::ToHex;

#[derive(Debug)]
enum Operation {
    NOP,
    HALT,
    MOV,
    LDF,
    STF,
    LDR,
    STR,
    ADD,
    SUB,
    MUL,
    MULU,
    DIV,
    MOD,
    AND,
    OR,
    EOR,
    NOT,
    LSL,
    LSR,
    ASR,
    ROL,
    ROR,
    CMP,
    B,
    BEQ,
    BNE,
}

#[derive(Debug)]
enum Reg {
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
}

fn register_number(r: &Reg) -> u16 {
    match r {
        Reg::R0 => 0b00000000_00000_000,
        Reg::R1 => 0b00000000_00000_001,
        Reg::R2 => 0b00000000_00000_010,
        Reg::R3 => 0b00000000_00000_011,
        Reg::R4 => 0b00000000_00000_100,
        Reg::R5 => 0b00000000_00000_101,
        Reg::R6 => 0b00000000_00000_110,
        Reg::R7 => 0b00000000_00000_111,
    }
}

fn to_operation(s: &str) -> Option<Operation> {
    match &s.to_uppercase()[..] {
        "NOP" => Some(Operation::NOP),
        "HALT" => Some(Operation::HALT),
        "MOV" => Some(Operation::MOV),
        "LDF" => Some(Operation::LDF),
        "STF" => Some(Operation::STF),
        "LDR" => Some(Operation::LDR),
        "STR" => Some(Operation::STR),
        "ADD" => Some(Operation::ADD),
        "SUB" => Some(Operation::SUB),
        "MUL" => Some(Operation::MUL),
        "MULU" => Some(Operation::MULU),
        "DIV" => Some(Operation::DIV),
        "MOD" => Some(Operation::MOD),
        "AND" => Some(Operation::AND),
        "OR" => Some(Operation::OR),
        "EOR" => Some(Operation::EOR),
        "NOT" => Some(Operation::NOT),
        "LSL" => Some(Operation::LSL),
        "LSR" => Some(Operation::LSR),
        "ASR" => Some(Operation::ASR),
        "ROL" => Some(Operation::ROL),
        "ROR" => Some(Operation::ROR),
        "CMP" => Some(Operation::CMP),
        "B" => Some(Operation::B),
        "BEQ" => Some(Operation::BEQ),
        "BNE" => Some(Operation::BNE),
        _ => None,
    }
}

fn operation_to_string(op: &Operation) -> String {
    match op {
        Operation::NOP => String::from("NOP"),
        Operation::HALT => String::from("HALT"),
        Operation::MOV => String::from("MOV"),
        Operation::LDF => String::from("LDF"),
        Operation::STF => String::from("STF"),
        Operation::LDR => String::from("LDR"),
        Operation::STR => String::from("STR"),
        Operation::ADD => String::from("ADD"),
        Operation::SUB => String::from("SUB"),
        Operation::MUL => String::from("MUL"),
        Operation::MULU => String::from("MULU"),
        Operation::DIV => String::from("DIV"),
        Operation::MOD => String::from("MOD"),
        Operation::AND => String::from("AND"),
        Operation::OR => String::from("OR"),
        Operation::EOR => String::from("EOR"),
        Operation::NOT => String::from("NOT"),
        Operation::LSL => String::from("LSL"),
        Operation::LSR => String::from("LSR"),
        Operation::ASR => String::from("ASR"),
        Operation::ROL => String::from("ROL"),
        Operation::ROR => String::from("ROR"),
        Operation::CMP => String::from("CMP"),
        Operation::B => String::from("B"),
        Operation::BEQ => String::from("BEQ"),
        Operation::BNE => String::from("BNE"),
    }
}

fn to_register(s: &str) -> Option<Reg> {
    match &s.to_uppercase()[..] {
        "R0" => Some(Reg::R0),
        "R1" => Some(Reg::R1),
        "R2" => Some(Reg::R2),
        "R3" => Some(Reg::R3),
        "R4" => Some(Reg::R4),
        "R5" => Some(Reg::R5),
        "R6" => Some(Reg::R6),
        "R7" => Some(Reg::R7),
        _ => None,
    }
}

fn register_to_string(r: &Reg) -> String {
    match r {
        Reg::R0 => String::from("R0"),
        Reg::R1 => String::from("R1"),
        Reg::R2 => String::from("R2"),
        Reg::R3 => String::from("R3"),
        Reg::R4 => String::from("R4"),
        Reg::R5 => String::from("R5"),
        Reg::R6 => String::from("R6"),
        Reg::R7 => String::from("R7"),
    }
}

fn parse_signed(s: &str, base: u32) -> Option<u16> {
    match s.chars().nth(0) {
        Some(x) => {
            if x == '-' {
                parse_base(&s[1..], base).and_then(
                    |n| Some(!n + 1 & 0b00001111_11111111)
                    )
            } else {
                parse_base(&s, base)
            }
        },
        None => None,
    }
}

fn parse_base(s: &str, base: u32) -> Option<u16> {
    match u16::from_str_radix(s, base) {
        Ok(n) => {
            if n <= 0b00001111_11111111 {
                Some(n)
            } else {
                eprintln!("Immediate value `{}` cannot fit into 12 bits", s);
                process::exit(1);
            }
        },
        Err(e) => {
            if *e.kind() == PosOverflow {
                eprintln!("Immediate value `{}` cannot fit into 12 bits", s);
            } else {
                eprint!("Parsing immediate value `{}` ", s);
                eprintln!("failed with error:\n{}", e);
            }
            process::exit(1);
        }
    }
}

fn to_immediate(s: &str) -> Option<u16> {
    match s.chars().nth(0) {
        Some(x) => {
            match x {
                '0' => {
                    match s.chars().nth(1) {
                        Some('b') => parse_signed(&s[2..], 2),
                        Some('x') => parse_signed(&s[2..], 16),
                        None => Some(0),
                        _ => None,
                    }
                }
                '1'..='9' | '-' => parse_signed(&s, 10),
                '#' => parse_signed(&s[1..], 10),
                '$' => parse_signed(&s[1..], 16),
                '%' => parse_signed(&s[1..], 2),
                _ => None,
            }
        }
        None => None,
    }
}

fn immediate_to_string(im: &u16) -> String {
    if (im & 0b00001000_00000000) == 0 {
        format!("#{im}")
    } else {
        format!("#{}", (im | 0b11110000_00000000) as i16)
    }
}

#[derive(Debug)]
enum Token {
    Instruction(Operation),
    Register(Reg),
    Immediate(u16),
    LabelDef(String),
    Label(String),
}

#[derive(Debug)]
enum InstructionType {
    Zero,
    Reg,
    Im,
    TwoReg,
    RegIm,
    ThreeReg,
}

fn instruction_type(t: &Vec<Token>) -> InstructionType {
    match t.len() {
        0 => panic!("This line should never execute"),
        1 => {
            match &t[..] {
                [Token::Instruction(_)] => InstructionType::Zero,
                [x] => {
                    eprintln!("Expected instruction, found `{:?}`", x);
                    process::exit(1);
                },
                _ => panic!("This line should never execute"),
            }
        },
        2 => {
            match &t[..] {
                [Token::Instruction(_), Token::Register(_)] =>
                    InstructionType::Reg,
                [Token::Instruction(_), Token::Immediate(_)] =>
                    InstructionType::Im,
                [Token::Instruction(_), x] => {
                    eprintln!("Invalid argument: `{:?}`", x);
                    process::exit(1);
                },
                [x, _] => {
                    eprintln!("Expected instruction, found `{:?}`", x);
                    process::exit(1);
                },
                _ => panic!("This line should never execute"),
            }
        },
        3 => {
            match &t[..] {
                [Token::Instruction(_), Token::Register(_),
                    Token::Register(_)] => InstructionType::TwoReg,
                [Token::Instruction(_), Token::Register(_),
                    Token::Immediate(_)] => InstructionType::RegIm,
                [Token::Instruction(_), Token::Register(_), x] => {
                    eprintln!("Invalid argument: `{:?}`", x);
                    process::exit(1);
                },
                [Token::Instruction(_), x, _] => {
                    eprintln!("Invalid argument: `{:?}`", x);
                    process::exit(1);
                },
                [x, _, _] => {
                    eprintln!("Expected instruction, found `{:?}`", x);
                    process::exit(1);
                },
                _ => panic!("This line should never execute"),

            }
        },
        4 => {
            match &t[..] {
                [Token::Instruction(_), Token::Register(_),
                    Token::Register(_), Token::Register(_)] =>
                        InstructionType::ThreeReg,
                [Token::Instruction(_), Token::Register(_),
                    Token::Register(_), x] => {
                    eprintln!("Invalid argument: `{:?}`", x);
                    process::exit(1);
                },
                [Token::Instruction(_), Token::Register(_), x, _] => {
                    eprintln!("Invalid argument: `{:?}`", x);
                    process::exit(1);
                },
                [Token::Instruction(_), x, _, _] => {
                    eprintln!("Invalid argument: `{:?}`", x);
                    process::exit(1);
                },
                [x, _, _, _] => {
                    eprintln!("Expected instruction, found `{:?}`", x);
                    process::exit(1);
                },
                _ => panic!("This line should never execute"),
            }
        },
        _ => {
            eprintln!("Too many arguments");
            process::exit(1);
        },
    }
}

fn opcode(op: &Operation, i: &InstructionType) -> u16 {
    match (op, i) {
        (Operation::NOP, InstructionType::Zero) => 0b000_0000_000000000,
        (Operation::HALT, InstructionType::Zero) => 0b000_0011_000000000,
        (Operation::MOV, InstructionType::TwoReg) => 0b000_0100_000000000,
        (Operation::LDF, InstructionType::Reg) => 0b000_0110_000000000,
        (Operation::STF, InstructionType::Reg) => 0b000_0111_000000000,
        (Operation::LDR, InstructionType::ThreeReg) => 0b000_1000_000000000,
        (Operation::LDR, InstructionType::TwoReg) => 0b000_1011_000000000,
        (Operation::STR, InstructionType::ThreeReg) => 0b000_1100_000000000,
        (Operation::STR, InstructionType::TwoReg) => 0b000_1111_000000000,
        (Operation::ADD, InstructionType::ThreeReg) => 0b001_0000_000000000,
        (Operation::SUB, InstructionType::ThreeReg) => 0b001_0001_000000000,
        (Operation::MUL, InstructionType::ThreeReg) => 0b001_0010_000000000,
        (Operation::MULU, InstructionType::ThreeReg) => 0b001_0011_000000000,
        (Operation::DIV, InstructionType::ThreeReg) => 0b001_0100_000000000,
        (Operation::MOD, InstructionType::ThreeReg) => 0b001_0101_000000000,
        (Operation::AND, InstructionType::ThreeReg) => 0b001_0110_000000000,
        (Operation::OR, InstructionType::ThreeReg) => 0b001_0111_000000000,
        (Operation::EOR, InstructionType::ThreeReg) => 0b001_1000_000000000,
        (Operation::NOT, InstructionType::TwoReg) => 0b001_1001_000000000,
        (Operation::LSL, InstructionType::ThreeReg) => 0b001_1010_000000000,
        (Operation::LSR, InstructionType::ThreeReg) => 0b001_1011_000000000,
        (Operation::ASR, InstructionType::ThreeReg) => 0b001_1100_000000000,
        (Operation::ROL, InstructionType::ThreeReg) => 0b001_1101_000000000,
        (Operation::ROR, InstructionType::ThreeReg) => 0b001_1110_000000000,
        (Operation::CMP, InstructionType::TwoReg) => 0b001_1111_000000000,
        (Operation::B, InstructionType::Im) => 0b01_00_0000_00000000,
        (Operation::BEQ, InstructionType::Im) => 0b01_10_0000_00000000,
        (Operation::BNE, InstructionType::Im) => 0b01_11_0000_00000000,
        (Operation::MOV, InstructionType::RegIm) => 0b1_000_0000_00000000,
        _ => {
            eprintln!("Invalid arguments for instruction `{}`",
                      operation_to_string(op));
            process::exit(1);
        },
    }
}

fn read_lines<P>(filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
where P: AsRef<Path>, {
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}

fn parse(infile: String) -> Vec<Vec<Token>> {
    let mut thing: Vec<Vec<Token>> = vec![];
    if let Ok(lines) = read_lines(infile) {
        for line in lines {
            if let Ok(x) = line {
                let mut otherthing: Vec<Token> = vec![];
                for to in x.split_whitespace() {
                    let t = String::from(to);
                    let len = t.as_bytes().len();
                    if t.as_bytes()[0] == ";".as_bytes()[0] {
                        break;
                    } else if t.as_bytes()[len - 1] == ":".as_bytes()[0] {
                        otherthing.push(Token::LabelDef(t));
                    } else if let Some(op) = to_operation(&t) {
                        otherthing.push(Token::Instruction(op));
                    } else if let Some(r) = to_register(&t) {
                        otherthing.push(Token::Register(r));
                    } else if let Some(im) = to_immediate(&t) {
                        otherthing.push(Token::Immediate(im));
                    } else {
                        otherthing.push(Token::Label(t));
                    }
                    //println!("{:?}", otherthing);
                }
                if otherthing.len() > 0 {
                    thing.push(otherthing);
                }
                //println!("{:?}", thing);
            }
        }
    }
    thing
}

fn generate_table(thing: &mut Vec<Vec<Token>>) -> HashMap<String, u16> {
    let mut table: HashMap<String, u16> = HashMap::new();
    let mut i: u16 = 0;
    while (i as usize) < thing.len() {
        let mut j: usize = 0;
        while j < thing[i as usize].len() {
            if let Token::LabelDef(la) = &thing[i as usize][j] {
                let la = String::from(&la[0..(la.len() - 1)]);
                if table.contains_key(&la) {
                    eprintln!("Multiple definitions of label: `{}`", la);
                    process::exit(1);
                } else {
                    table.insert(la, i);
                    thing[i as usize].remove(j);
                }
            } else {
                j += 1;
            }
        }
        if thing[i as usize].len() > 0 {
            i += 1;
        } else {
            thing.remove(i as usize);
        }
    }
    table
}

fn replace_labels(thing: &mut Vec<Vec<Token>>, table: &HashMap<String, u16>) {
    for i in 0..thing.len() {
        for j in 0..thing[i].len() {
            if let Token::Label(la) = &thing[i][j] {
                if let Some(&a) = table.get(la) {
                    let offset = a as i32 - (i as i32 + 1);
                    let of = if offset < 0 {
                        let o = offset * -1;
                        if o > 0b00001111_11111111 {
                            eprintln!(
                                "Offset of {} for label {} cannot fit into 12 bits",
                                o, la
                            );
                            process::exit(1);
                        } else {
                            (offset as u16) & 0b00001111_11111111
                        }
                    } else {
                        if offset > 0b00001111_11111111 {
                            eprintln!(
                                "Offset of {} for label {} cannot fit into 12 bits",
                                offset, la
                            );
                            process::exit(1);
                        } else {
                            offset as u16
                        }
                    };
                    thing[i][j] = Token::Immediate(of);
                } else {
                    eprintln!("Cannot find definition for label: `{la}`");
                    process::exit(1);
                }
            }
        }
    }
}

fn get_label(table: &HashMap<String, u16>, ad: u16) -> String {
    for (label, &address) in table {
        if address == ad {
            return label.clone();
        }
    }
    panic!("Unable to find label for address: `{ad}`");
}

fn assemble(thing: &Vec<Vec<Token>>, table: &HashMap<String, u16>,
            listing: bool) -> Vec<u16> {
    let mut ass: Vec<u16> = vec![];
    for i in 0..thing.len() {
        let in_type = instruction_type(&thing[i]);
        if let Token::Instruction(inst) = &thing[i][0] {
            let mut args = String::from("");
            let mut word = opcode(&inst, &in_type);
            match in_type {
                InstructionType::Zero => { /* Do nothing */ },
                InstructionType::Reg => {
                    if let Token::Register(r) = &thing[i][1] {
                        let rg = register_number(r);
                        args = register_to_string(r);
                        let rg = match inst {
                            Operation::LDF => rg << 3,
                            Operation::STF => rg << 6,
                            _ => panic!("This line should never execute"),
                        };
                        word |= rg;
                    }
                },
                InstructionType::Im => {
                    if let Token::Immediate(im) = &thing[i][1] {
                        let a = immediate_to_string(im);
                        let len = a.len();
                        let offset = a[1..len].parse::<i32>().unwrap();
                        let ad = (i as i32 + 1 + offset) as u16;
                        args = get_label(table, ad);
                        word |= im;
                    }
                },
                InstructionType::TwoReg => {
                    if let Token::Register(r1) = &thing[i][1] {
                        let rg1 = register_number(r1);
                        if let Token::Register(r2) = &thing[i][2] {
                            let rg2 = register_number(r2);
                            args = format!("{} {}", register_to_string(r1),
                                register_to_string(r2));
                            let (rg1, rg2) = match inst {
                                Operation::CMP => (rg1 << 6, rg2),
                                _ => (rg1 << 3, rg2 << 6),
                            };
                            word |= rg1;
                            word |= rg2;
                        }
                    }
                },
                InstructionType::RegIm => {
                    if let Token::Register(rd) = &thing[i][1] {
                        let rgd = register_number(rd) << 12;
                        if let Token::Immediate(im) = &thing[i][2] {
                            args = format!("{} {}", register_to_string(rd),
                                immediate_to_string(im));
                            word |= rgd;
                            word |= im;
                        }
                    }
                },
                InstructionType::ThreeReg => {
                    if let Token::Register(rd) = &thing[i][1] {
                        let rgd = register_number(rd) << 3;
                        if let Token::Register(rn) = &thing[i][2] {
                            let rgn = register_number(rn) << 6;
                            if let Token::Register(rm) = &thing[i][3] {
                                let rgm = register_number(rm);
                                args = format!(
                                    "{} {} {}",
                                    register_to_string(rd),
                                    register_to_string(rn),
                                    register_to_string(rm)
                                );
                                word |= rgd;
                                word |= rgn;
                                word |= rgm;
                            }
                        }
                    }
                },
            }
            if listing {
                eprintln!("{}:{}\t{} {}", i,
                         word.to_be_bytes().encode_hex_upper::<String>(),
                         operation_to_string(inst), args
                );
            }
            ass.push(word);
        }
    }
    ass
}

fn ass_to_bytes(ass: &Vec<u16>) -> Vec<u8> {
    let mut bytes = vec![];
    for i in ass {
        let b = i.to_be_bytes();
        bytes.push(b[0]);
        bytes.push(b[1]);
    }
    bytes
}

fn to_logisim_hex(s: String) -> Vec<u8> {
    let s = s.as_bytes();
    let mut v: Vec<u8> = "v2.0 raw\n".as_bytes().to_vec();
    let mut i = 0;
    while i < s.len() {
        v.push(s[i]);
        i += 1;
        v.push(s[i]);
        i += 1;
        v.push(s[i]);
        i += 1;
        v.push(s[i]);
        i += 1;
        v.push(10);
    }
    v
}

fn write(ass: &Vec<u16>, outfile: String) {
    let mut file = File::create(outfile).unwrap();
    file.write_all(&to_logisim_hex(
            (&ass_to_bytes(ass)[..])
            .encode_hex_upper::<String>())[..]
        ).unwrap();
}

fn print_usage() {
    eprintln!("USAGE:  alarmas <source file> <object file> [-l]");
    eprintln!("       -l : print listing to standard error\n");
}

struct Arguments {
    infile: String,
    outfile: String,
    listing: bool,
}

impl Arguments {
    fn new(mut args: impl Iterator<Item = String>) -> Arguments {
        let mut infile = None;
        let mut outfile = None;
        let mut listing = false;
        args.next();
        loop {
            match args.next() {
                Some(arg) => {
                    if arg.as_bytes() == "-l".as_bytes() {
                        listing = true;
                    } else {
                        match infile {
                            Some(_) => {
                                match outfile {
                                    Some(_) => {
                                        eprintln!("Too many arguments");
                                        print_usage();
                                        process::exit(1);
                                    },
                                    None => outfile = Some(arg)
                                }
                            },
                            None => infile = Some(arg),
                        }
                    }
                },
                None => break,
            }
        }
        match (infile, outfile) {
            (Some(inf), Some(outf)) => {
                Arguments{
                    infile: inf,
                    outfile: outf,
                    listing,
                }
            },
            _ => {
                eprintln!("Too few arguments");
                print_usage();
                process::exit(1);
            },
        }
    }
}

fn main() {
    let args = Arguments::new(env::args());
    let mut thing = parse(args.infile);
    let table = generate_table(&mut thing);
    replace_labels(&mut thing, &table);
    if thing.len() > 65535 {
        eprintln!("Instruction memory is too large");
        eprintln!("{} lines cannot fit into 16 bits", thing.len());
        process::exit(1);
    }
    if args.listing {
        eprintln!("*** LABEL LIST ***");
        for (label, address) in &table {
            eprintln!("{}\t{}", label, address);
        }
        eprintln!("*** MACHINE PROGRAM ***");
    }
    let ass = assemble(&thing, &table, args.listing);
    write(&ass, args.outfile);
}
