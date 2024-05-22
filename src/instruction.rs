use std::fmt::Display;

#[derive(Copy, Clone, Debug)]
pub enum AddressingMode {
    Accumulator,
    Absolute,
    AbsoluteX,
    AbsoluteY,
    Immediate,
    Implied,
    Indirect,
    IndirectX,
    IndirectY,
    Relative,
    ZeroPage,
    ZeroPageX,
    ZeroPageY,
}

impl Display for AddressingMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                AddressingMode::Accumulator => "A",
                AddressingMode::Absolute => "abs",
                AddressingMode::AbsoluteX => "abs,X",
                AddressingMode::AbsoluteY => "abs,Y",
                AddressingMode::Immediate => "#",
                AddressingMode::Implied => "impl",
                AddressingMode::Indirect => "ind",
                AddressingMode::IndirectX => "X,ind",
                AddressingMode::IndirectY => "ind,Y",
                AddressingMode::Relative => "rel",
                AddressingMode::ZeroPage => "zpg",
                AddressingMode::ZeroPageX => "zpg,X",
                AddressingMode::ZeroPageY => "zpg,Y",
            }
        )
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Instruction {
    pub op: Operation,
    pub addressing_mode: AddressingMode,
}

impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {}",
            format!("{:?}", self.op).to_lowercase(),
            self.addressing_mode
        )
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Operation {
    /// add with carry
    ADC,
    /// and (with accumulator)
    AND,
    /// arithmetic shift left
    ASL,
    /// branch on carry clear
    BCC,
    /// branch on carry set
    BCS,
    /// branch on equal (zero set)
    BEQ,
    /// bit test
    BIT,
    /// branch on minus (negative set)
    BMI,
    /// branch on not equal (zero clear)
    BNE,
    /// branch on plus (negative clear)
    BPL,
    /// break / interrupt
    BRK,
    /// branch on overflow clear
    BVC,
    /// branch on overflow set
    BVS,
    /// clear carry
    CLC,
    /// clear decimal
    CLD,
    /// clear interrupt disable
    CLI,
    /// clear overflow
    CLV,
    /// compare (with accumulator)
    CMP,
    /// compare with X
    CPX,
    /// compare with Y
    CPY,
    /// decrement
    DEC,
    /// decrement X
    DEX,
    /// decrement Y
    DEY,
    /// exclusive or (with accumulator)
    EOR,
    /// increment
    INC,
    /// increment X
    INX,
    /// increment Y
    INY,
    /// jump
    JMP,
    /// jump subroutine
    JSR,
    /// load accumulator
    LDA,
    /// load X
    LDX,
    /// load Y
    LDY,
    /// logical shift right
    LSR,
    /// no operation
    NOP,
    /// or with accumulator
    ORA,
    /// push accumulator
    PHA,
    /// push processor status (SR)
    PHP,
    /// pull accumulator
    PLA,
    /// pull processor status (SR)
    PLP,
    /// rotate left
    ROL,
    /// rotate right
    ROR,
    /// return from interrupt
    RTI,
    /// return from subroutine
    RTS,
    /// subtract with carry
    SBC,
    /// set carry
    SEC,
    /// set decimal
    SED,
    /// set interrupt disable
    SEI,
    /// store accumulator
    STA,
    /// store X
    STX,
    /// store Y
    STY,
    /// transfer accumulator to X
    TAX,
    /// transfer accumulator to Y
    TAY,
    /// transfer stack pointer to X
    TSX,
    /// transfer X to accumulator
    TXA,
    /// transfer X to stack pointer
    TXS,
    /// transfer Y to accumulator
    TYA,
}

macro_rules! inst {
    ($op: ident A) => {
        Some(Instruction::new(
            Operation::$op,
            AddressingMode::Accumulator,
        ))
    };
    ($op: ident abs) => {
        Some(Instruction::new(Operation::$op, AddressingMode::Absolute))
    };
    ($op: ident abs,X) => {
        Some(Instruction::new(Operation::$op, AddressingMode::AbsoluteX))
    };
    ($op: ident abs,Y) => {
        Some(Instruction::new(Operation::$op, AddressingMode::AbsoluteY))
    };
    ($op: ident #) => {
        Some(Instruction::new(Operation::$op, AddressingMode::Immediate))
    };
    ($op: ident impl) => {
        Some(Instruction::new(Operation::$op, AddressingMode::Implied))
    };
    ($op: ident ind) => {
        Some(Instruction::new(Operation::$op, AddressingMode::Indirect))
    };
    ($op: ident X,ind) => {
        Some(Instruction::new(Operation::$op, AddressingMode::IndirectX))
    };
    ($op: ident ind,Y) => {
        Some(Instruction::new(Operation::$op, AddressingMode::IndirectY))
    };
    ($op: ident rel) => {
        Some(Instruction::new(Operation::$op, AddressingMode::Relative))
    };
    ($op: ident zpg) => {
        Some(Instruction::new(Operation::$op, AddressingMode::ZeroPage))
    };
    ($op: ident zpg,X) => {
        Some(Instruction::new(Operation::$op, AddressingMode::ZeroPageX))
    };
    ($op: ident zpg,Y) => {
        Some(Instruction::new(Operation::$op, AddressingMode::ZeroPageY))
    };
    (---) => {
        None
    };
}

/// Almost directly copy/pasted from https://www.masswerk.at/6502/6502_instruction_set.html
#[rustfmt::skip]
const INSTRUCTIONS: [Option<Instruction>; 256] = [
    inst!(BRK impl), inst!(ORA X,ind), inst!(---  ), inst!(---), inst!(---      ), inst!(ORA zpg  ), inst!(ASL zpg  ), inst!(---), inst!(PHP impl), inst!(ORA #    ), inst!(ASL A   ), inst!(---), inst!(---      ), inst!(ORA abs  ), inst!(ASL abs  ), inst!(---),
    inst!(BPL rel ), inst!(ORA ind,Y), inst!(---  ), inst!(---), inst!(---      ), inst!(ORA zpg,X), inst!(ASL zpg,X), inst!(---), inst!(CLC impl), inst!(ORA abs,Y), inst!(---     ), inst!(---), inst!(---      ), inst!(ORA abs,X), inst!(ASL abs,X), inst!(---),
    inst!(JSR abs ), inst!(AND X,ind), inst!(---  ), inst!(---), inst!(BIT zpg  ), inst!(AND zpg  ), inst!(ROL zpg  ), inst!(---), inst!(PLP impl), inst!(AND #    ), inst!(ROL A   ), inst!(---), inst!(BIT abs  ), inst!(AND abs  ), inst!(ROL abs  ), inst!(---),
    inst!(BMI rel ), inst!(AND ind,Y), inst!(---  ), inst!(---), inst!(---      ), inst!(AND zpg,X), inst!(ROL zpg,X), inst!(---), inst!(SEC impl), inst!(AND abs,Y), inst!(---     ), inst!(---), inst!(---      ), inst!(AND abs,X), inst!(ROL abs,X), inst!(---),
    inst!(RTI impl), inst!(EOR X,ind), inst!(---  ), inst!(---), inst!(---      ), inst!(EOR zpg  ), inst!(LSR zpg  ), inst!(---), inst!(PHA impl), inst!(EOR #    ), inst!(LSR A   ), inst!(---), inst!(JMP abs  ), inst!(EOR abs  ), inst!(LSR abs  ), inst!(---),
    inst!(BVC rel ), inst!(EOR ind,Y), inst!(---  ), inst!(---), inst!(---      ), inst!(EOR zpg,X), inst!(LSR zpg,X), inst!(---), inst!(CLI impl), inst!(EOR abs,Y), inst!(---     ), inst!(---), inst!(---      ), inst!(EOR abs,X), inst!(LSR abs,X), inst!(---),
    inst!(RTS impl), inst!(ADC X,ind), inst!(---  ), inst!(---), inst!(---      ), inst!(ADC zpg  ), inst!(ROR zpg  ), inst!(---), inst!(PLA impl), inst!(ADC #    ), inst!(ROR A   ), inst!(---), inst!(JMP ind  ), inst!(ADC abs  ), inst!(ROR abs  ), inst!(---),
    inst!(BVS rel ), inst!(ADC ind,Y), inst!(---  ), inst!(---), inst!(---      ), inst!(ADC zpg,X), inst!(ROR zpg,X), inst!(---), inst!(SEI impl), inst!(ADC abs,Y), inst!(---     ), inst!(---), inst!(---      ), inst!(ADC abs,X), inst!(ROR abs,X), inst!(---),
    inst!(---     ), inst!(STA X,ind), inst!(---  ), inst!(---), inst!(STY zpg  ), inst!(STA zpg  ), inst!(STX zpg  ), inst!(---), inst!(DEY impl), inst!(---      ), inst!(TXA impl), inst!(---), inst!(STY abs  ), inst!(STA abs  ), inst!(STX abs  ), inst!(---),
    inst!(BCC rel ), inst!(STA ind,Y), inst!(---  ), inst!(---), inst!(STY zpg,X), inst!(STA zpg,X), inst!(STX zpg,Y), inst!(---), inst!(TYA impl), inst!(STA abs,Y), inst!(TXS impl), inst!(---), inst!(---      ), inst!(STA abs,X), inst!(---      ), inst!(---),
    inst!(LDY #   ), inst!(LDA X,ind), inst!(LDX #), inst!(---), inst!(LDY zpg  ), inst!(LDA zpg  ), inst!(LDX zpg  ), inst!(---), inst!(TAY impl), inst!(LDA #    ), inst!(TAX impl), inst!(---), inst!(LDY abs  ), inst!(LDA abs  ), inst!(LDX abs  ), inst!(---),
    inst!(BCS rel ), inst!(LDA ind,Y), inst!(---  ), inst!(---), inst!(LDY zpg,X), inst!(LDA zpg,X), inst!(LDX zpg,Y), inst!(---), inst!(CLV impl), inst!(LDA abs,Y), inst!(TSX impl), inst!(---), inst!(LDY abs,X), inst!(LDA abs,X), inst!(LDX abs,Y), inst!(---),
    inst!(CPY #   ), inst!(CMP X,ind), inst!(---  ), inst!(---), inst!(CPY zpg  ), inst!(CMP zpg  ), inst!(DEC zpg  ), inst!(---), inst!(INY impl), inst!(CMP #    ), inst!(DEX impl), inst!(---), inst!(CPY abs  ), inst!(CMP abs  ), inst!(DEC abs  ), inst!(---),
    inst!(BNE rel ), inst!(CMP ind,Y), inst!(---  ), inst!(---), inst!(---      ), inst!(CMP zpg,X), inst!(DEC zpg,X), inst!(---), inst!(CLD impl), inst!(CMP abs,Y), inst!(---     ), inst!(---), inst!(---      ), inst!(CMP abs,X), inst!(DEC abs,X), inst!(---),
    inst!(CPX #   ), inst!(SBC X,ind), inst!(---  ), inst!(---), inst!(CPX zpg  ), inst!(SBC zpg  ), inst!(INC zpg  ), inst!(---), inst!(INX impl), inst!(SBC #    ), inst!(NOP impl), inst!(---), inst!(CPX abs  ), inst!(SBC abs  ), inst!(INC abs  ), inst!(---),
    inst!(BEQ rel ), inst!(SBC ind,Y), inst!(---  ), inst!(---), inst!(---      ), inst!(SBC zpg,X), inst!(INC zpg,X), inst!(---), inst!(SED impl), inst!(SBC abs,Y), inst!(---     ), inst!(---), inst!(---      ), inst!(SBC abs,X), inst!(INC abs,X), inst!(---),
];

impl Instruction {
    const fn new(op: Operation, addressing_mode: AddressingMode) -> Self {
        Self {
            op,
            addressing_mode,
        }
    }

    pub fn from_byte(byte: u8) -> Option<Self> {
        INSTRUCTIONS[byte as usize]
    }
}
