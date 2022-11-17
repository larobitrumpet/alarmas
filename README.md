# alARM Assembler

This is an assembler for a 16 bit alARM CPU written in rust.

## Assembly Language

Labels are strings that don't start with a `#` and don't contain whitespace or `;`. Label definitions end with a `:`. Registers are defined with an `R` or `r` followed by the register number, for example `R0` is register number 0. Immediate values are in decimal and start with a `#` followed by an optional `-` to indicate a negative number follwed by the value, for example `#15` is the number 15 and `#-12` is the number -12. Comments start with a `;` and end with a newline. Operations can be uppercase or lowercase and are defined in the table below. Rd, Rn, and Rm are registers and Im is an immediate value.

| Instruction | Description |
|-------------|-------------|
| NOP  | No operation, does nothing |
| HALT | Halts the cpu, stops the clock |
| MOV Rd Rn | Moves the contents of Rn into Rd |
| LDF Rd | Moves the lower 4 bits of Rd into the flags |
| STF Rd | Moves the flags into the lower 4 bits of Rd |
| LDR Rd Rn Rm | Loads the contents of data memory located at an address defined by the contents of Rn plus the contents of Rm into Rd |
| LDR Rd Rn | Loads the contents of data memory located at an address defined by the contents of Rn |
| STR Rd Rn Rm | Loads the contents of Rd into data memory located at an address defined by the contents of Rn plus the contents of Rm |
| STD Rn Rn | Loads the contents of Rd into data memory located at an address defined by the contents of Rn |
| ADD Rd Rn Rm | Rd <\- Rn + Rm + C (C = carry flag) |
| SUB Rd Rn Rm | Rd <\- Rn - Rm |
| MUL Rd Rn Rm | Rd <\- the lower 16 bits of Rn * Rm |
| MULU Rd Rn Rm | Rd <\- the upper 16 bits of Rn * Rm |
| DIV Rd Rn Rm | Rd <\- Rn / Rm |
| MOD Rd Rn Rm | Rd <\- Rn mod Rm |
| AND Rd Rn Rm | Rd <\- Rn bitwise AND Rm |
| OR Rd Rn Rm | Rd <\- Rn bitwise OR Rm |
| EOR Rd Rn Rm | Rd <\- Rn bitwise exclusive OR Rm |
| NOT Rd Rn | Rd <\- bitwise not Rn |
| LSL Rd Rn Rm | Rd <\- Rn logical shifted left by the lower 4 bits of of Rm |
| LSR Rd Rn Rm | Rd <\- Rn logical shifted right by the lower 4 bits of Rm |
| ASR Rd Rn Rm | Rd <\- Rn arithmetic shifted right by the lower 4 bits of Rm |
| ROL Rd Rn Rm | Rd <\- Rn rotated left by the lower 4 bits of Rm |
| ROR Rd Rn Rm | Rd <\- Rn rotated right by the lower 4 bits of Rm |
| CMP Rn Rm | Compares Rn Rm by subtracting Rn and Rm and setting the flags |
| B Im | Unconditional branch to PC + 1 + Im |
| BEQ Im | Branches to PC + 1 + Im if the zero flag is set |
| BNE Im | Branches to PC + 1 + Im if the zero flag is cleared |
| MOV Rd Im | Moves the immediate value Im into the register Rd |

## Build

To build from source, [install Rust](https://www.rust-lang.org/learn/get-started) and run `cargo build --release`. An executable will be created under `target/release/`. You can run it with `cargo run --release <source file> <object file> [-l]`, or just run the executable directly `alarmas <source file> <object file> [-l]`. `<source file>` is a path to an assembly source file, `<object file>` is a path to an object file that the assembler to write to, and the `-l` prints a listing to standard error.
