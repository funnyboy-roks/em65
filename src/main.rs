use std::{
    fs,
    io::{Read, Write},
    num::Wrapping,
    ops::Deref,
};

use anyhow::Context;

pub mod instruction;

use instruction::{AddressingMode, Instruction, Operation};

bitflags::bitflags! {
    #[derive(Copy, Clone, Debug, Default)]
    pub struct Status: u8 {
        const CARRY        = 0b00000001;
        const ZERO         = 0b00000010;
        const IRQB_DISABLE = 0b00000100;
        const DECIMAL      = 0b00001000;
        const BRK          = 0b00010000;

        const OVERFLOW     = 0b01000000;
        const NEGATIVE     = 0b10000000;
    }
}

pub trait Bus {
    fn read(&self, address: u16) -> u8;
    fn write(&mut self, address: u16, byte: u8);

    fn read_u16(&self, address: u16) -> u16 {
        u16::from_le_bytes([self.read(address), self.read(address + 1)])
    }
}

#[derive(Copy, Clone, Debug)]
pub struct MyBus {
    rom: ROM,
    ram: [u8; 32 * 1024],
}

impl Bus for MyBus {
    fn read(&self, address: u16) -> u8 {
        match address {
            0x0000..=0x01ff => self.ram[address as usize],
            0x8000.. => self.rom[address as usize - 0x8000],
            a => {
                eprintln!("Unknown address ${:04x}, assuming RAM", address);
                self.ram[a as usize]
            }
        }
    }

    fn write(&mut self, address: u16, byte: u8) {
        match address {
            0x0000..=0x01ff => self.ram[address as usize] = byte,
            0x2000 => {
                let mut stdio = std::io::stdout().lock();
                if byte.is_ascii() {
                    stdio.write(&[byte]).unwrap();
                    stdio.flush().unwrap();
                } else {
                    panic!("tried to write non-ascii byte to console: {:02x}", byte);
                }
            }
            0x2001 => {
                println!("0b{:08b}", byte);
            }
            0x2002 => {
                println!("0x{:02x}", byte);
            }
            0x8000.. => panic!("write to ROM not allowed."),
            a => {
                eprintln!("Unknown address ${:04x}, assuming RAM", address);
                self.ram[a as usize] = byte;
            }
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct MOS6502<B> {
    pub accumulator: Wrapping<u8>,
    pub y: Wrapping<u8>,
    pub x: Wrapping<u8>,
    /// Program counter
    pub pc: u16,
    /// Lower byte of stack pointer (top byte is always 1)
    pub stack_pointer: u8,
    pub status: Status,
    pub bus: B,
}

impl<B> MOS6502<B>
where
    B: Bus,
{
    pub fn new(bus: B) -> Self {
        Self {
            accumulator: Wrapping(0),
            y: Wrapping(0),
            x: Wrapping(0),
            pc: 0,
            stack_pointer: 255,
            status: Status::empty(),
            bus,
        }
    }

    pub fn read_instruction(&mut self) -> Option<Instruction> {
        let inst_byte = self.bus.read(self.pc);
        // eprintln!("inst_byte = 0x{:02x}", inst_byte);
        Instruction::from_byte(inst_byte)
    }

    fn read_curr(&mut self) -> u8 {
        let o = self.bus.read(self.pc);
        self.pc += 1;
        o
    }

    fn read_curr_u16(&mut self) -> u16 {
        let o = self.bus.read_u16(self.pc);
        self.pc += 2;
        o
    }

    fn push_stack_u8(&mut self, byte: u8) {
        self.stack_pointer -= 1;
        self.bus.write(0x0100 + self.stack_pointer as u16, byte);
    }

    fn push_stack<const N: usize>(&mut self, bytes: [u8; N]) {
        for b in bytes {
            self.push_stack_u8(b);
        }
    }

    fn pop_stack_u8(&mut self) -> u8 {
        let out = self.bus.read(0x0100 + self.stack_pointer as u16);
        self.stack_pointer = self.stack_pointer.wrapping_add(1);
        out
    }

    fn pop_stack<const N: usize>(&mut self) -> [u8; N] {
        let mut out = [0u8; N];
        for b in (0..N).rev() {
            out[b] = self.pop_stack_u8();
        }
        out
    }

    fn update_zero(&mut self, byte: u8) {
        self.status.set(Status::ZERO, byte == 0);
    }

    fn update_neg(&mut self, byte: u8) {
        self.status.set(Status::NEGATIVE, byte & 0b1000_0000 != 0);
    }

    pub fn run(&mut self) -> anyhow::Result<()> {
        // Read reset vec
        self.pc = u16::from_le_bytes([self.bus.read(0xfffc), self.bus.read(0xfffd)]);
        while !self.status.intersects(Status::BRK) {
            let inst = self.read_instruction().context("Invalid instruction")?;
            self.pc += 1;
            // eprintln!("inst = {}", inst);
            match inst.op {
                Operation::ADC => todo!("Instruction NYI: {}", inst),
                Operation::AND => todo!("Instruction NYI: {}", inst),
                Operation::ASL => todo!("Instruction NYI: {}", inst),
                Operation::BCC => match inst.addressing_mode {
                    AddressingMode::Accumulator => todo!(),
                    AddressingMode::Absolute => todo!(),
                    AddressingMode::AbsoluteX => todo!(),
                    AddressingMode::AbsoluteY => todo!(),
                    AddressingMode::Immediate => todo!(),
                    AddressingMode::Implied => todo!(),
                    AddressingMode::Indirect => todo!(),
                    AddressingMode::IndirectX => todo!(),
                    AddressingMode::IndirectY => todo!(),
                    AddressingMode::Relative => {
                        let add = self.bus.read(self.pc);
                        if !self.status.intersects(Status::CARRY) {
                            self.pc = self.pc.wrapping_add_signed((add as i8).into());
                        }
                        self.pc += 1;
                    }
                    AddressingMode::ZeroPage => todo!(),
                    AddressingMode::ZeroPageX => todo!(),
                    AddressingMode::ZeroPageY => todo!(),
                },
                Operation::BCS => todo!("Instruction NYI: {}", inst),
                Operation::BEQ => match inst.addressing_mode {
                    AddressingMode::Accumulator => todo!(),
                    AddressingMode::Absolute => todo!(),
                    AddressingMode::AbsoluteX => todo!(),
                    AddressingMode::AbsoluteY => todo!(),
                    AddressingMode::Immediate => todo!(),
                    AddressingMode::Implied => todo!(),
                    AddressingMode::Indirect => todo!(),
                    AddressingMode::IndirectX => todo!(),
                    AddressingMode::IndirectY => todo!(),
                    AddressingMode::Relative => {
                        let add = self.bus.read(self.pc);
                        if self.status.intersects(Status::ZERO) {
                            self.pc = self.pc.wrapping_add_signed((add as i8).into());
                        }
                        self.pc += 1;
                    }
                    AddressingMode::ZeroPage => todo!(),
                    AddressingMode::ZeroPageX => todo!(),
                    AddressingMode::ZeroPageY => todo!(),
                },
                Operation::BIT => todo!("Instruction NYI: {}", inst),
                Operation::BMI => todo!("Instruction NYI: {}", inst),
                Operation::BNE => match inst.addressing_mode {
                    AddressingMode::Accumulator => todo!(),
                    AddressingMode::Absolute => todo!(),
                    AddressingMode::AbsoluteX => todo!(),
                    AddressingMode::AbsoluteY => todo!(),
                    AddressingMode::Immediate => todo!(),
                    AddressingMode::Implied => todo!(),
                    AddressingMode::Indirect => todo!(),
                    AddressingMode::IndirectX => todo!(),
                    AddressingMode::IndirectY => todo!(),
                    AddressingMode::Relative => {
                        let add = self.bus.read(self.pc);
                        if !self.status.intersects(Status::ZERO) {
                            self.pc = self.pc.wrapping_add_signed((add as i8).into());
                        }
                        self.pc += 1;
                    }
                    AddressingMode::ZeroPage => todo!(),
                    AddressingMode::ZeroPageX => todo!(),
                    AddressingMode::ZeroPageY => todo!(),
                },
                Operation::BPL => todo!("Instruction NYI: {}", inst),
                Operation::BRK => match inst.addressing_mode {
                    AddressingMode::Implied => {
                        self.status |= Status::BRK;
                    }
                    _ => unreachable!(),
                },
                Operation::BVC => todo!("Instruction NYI: {}", inst),
                Operation::BVS => todo!("Instruction NYI: {}", inst),
                Operation::CLC => match inst.addressing_mode {
                    AddressingMode::Implied => self.status.remove(Status::DECIMAL),
                    _ => unreachable!(),
                },
                Operation::CLD => match inst.addressing_mode {
                    AddressingMode::Implied => self.status.remove(Status::DECIMAL),
                    _ => unreachable!(),
                },
                Operation::CLI => todo!("Instruction NYI: {}", inst),
                Operation::CLV => todo!("Instruction NYI: {}", inst),
                Operation::CMP => match inst.addressing_mode {
                    AddressingMode::Accumulator => todo!(),
                    AddressingMode::Absolute => todo!(),
                    AddressingMode::AbsoluteX => todo!(),
                    AddressingMode::AbsoluteY => todo!(),
                    AddressingMode::Immediate => {
                        let val = self.read_curr();
                        let (n, o) = self.accumulator.0.overflowing_sub(val);
                        self.update_zero(n);
                        self.update_neg(n);
                        self.status.set(Status::CARRY, o || n == 0);
                    }
                    AddressingMode::ZeroPage => todo!(),
                    AddressingMode::ZeroPageX => todo!(),
                    _ => unreachable!(),
                },
                Operation::CPX => match inst.addressing_mode {
                    AddressingMode::Accumulator => todo!(),
                    AddressingMode::Absolute => todo!(),
                    AddressingMode::AbsoluteX => todo!(),
                    AddressingMode::AbsoluteY => todo!(),
                    AddressingMode::Immediate => {
                        let val = self.read_curr();
                        let (n, o) = self.x.0.overflowing_sub(val);
                        self.update_zero(n);
                        self.update_neg(n);
                        self.status.set(Status::CARRY, o || n == 0);
                    }
                    AddressingMode::ZeroPage => todo!(),
                    AddressingMode::ZeroPageX => todo!(),
                    _ => unreachable!(),
                },
                Operation::CPY => match inst.addressing_mode {
                    AddressingMode::Accumulator => todo!(),
                    AddressingMode::Absolute => todo!(),
                    AddressingMode::AbsoluteX => todo!(),
                    AddressingMode::AbsoluteY => todo!(),
                    AddressingMode::Immediate => {
                        let val = self.read_curr();
                        let (n, o) = self.y.0.overflowing_sub(val);
                        self.update_zero(n);
                        self.update_neg(n);
                        self.status.set(Status::CARRY, o || n == 0);
                    }
                    AddressingMode::ZeroPage => todo!(),
                    AddressingMode::ZeroPageX => todo!(),
                    _ => unreachable!(),
                },
                Operation::DEC => todo!("Instruction NYI: {}", inst),
                Operation::DEX => match inst.addressing_mode {
                    AddressingMode::Implied => self.x -= 1,
                    _ => unreachable!(),
                },
                Operation::DEY => todo!("Instruction NYI: {}", inst),
                Operation::EOR => todo!("Instruction NYI: {}", inst),
                Operation::INC => match inst.addressing_mode {
                    AddressingMode::Accumulator => todo!(),
                    AddressingMode::Absolute => todo!(),
                    AddressingMode::AbsoluteX => todo!(),
                    AddressingMode::AbsoluteY => todo!(),
                    AddressingMode::Immediate => todo!(),
                    AddressingMode::Implied => todo!(),
                    AddressingMode::Indirect => todo!(),
                    AddressingMode::IndirectX => todo!(),
                    AddressingMode::IndirectY => todo!(),
                    AddressingMode::Relative => todo!(),
                    AddressingMode::ZeroPage => {
                        let pos = self.read_curr() as u16;
                        let prev = self.bus.read(pos);
                        let new = prev.wrapping_add(1);
                        self.update_zero(new);
                        self.update_neg(new);
                        self.bus.write(pos, new);
                    }
                    AddressingMode::ZeroPageX => todo!(),
                    AddressingMode::ZeroPageY => todo!(),
                },
                Operation::INX => match inst.addressing_mode {
                    AddressingMode::Implied => {
                        self.x += 1;
                        self.update_zero(self.x.0);
                        self.update_neg(self.x.0);
                    }
                    _ => unreachable!(),
                },
                Operation::INY => match inst.addressing_mode {
                    AddressingMode::Implied => {
                        self.y += 1;
                        self.update_zero(self.y.0);
                        self.update_neg(self.y.0);
                    }
                    _ => unreachable!(),
                },
                Operation::JMP => match inst.addressing_mode {
                    AddressingMode::Absolute => {
                        self.pc = self.read_curr_u16();
                    }
                    AddressingMode::Indirect => todo!(),
                    AddressingMode::IndirectX => todo!(),
                    AddressingMode::IndirectY => todo!(),
                    _ => unreachable!(),
                },
                Operation::JSR => match inst.addressing_mode {
                    AddressingMode::Absolute => {
                        self.push_stack((self.pc + 2).to_le_bytes());
                        self.pc = self.read_curr_u16();
                    }
                    _ => unreachable!(),
                },
                Operation::LDA => {
                    match inst.addressing_mode {
                        AddressingMode::Accumulator => todo!(),
                        AddressingMode::Absolute => todo!(),
                        AddressingMode::AbsoluteX => todo!(),
                        AddressingMode::AbsoluteY => todo!(),
                        AddressingMode::Immediate => {
                            self.accumulator.0 = self.read_curr();
                        }
                        AddressingMode::Implied => todo!(),
                        AddressingMode::Indirect => todo!(),
                        AddressingMode::IndirectX => todo!(),
                        AddressingMode::IndirectY => {
                            let curr = self.read_curr();
                            // eprintln!("lda (${:02x}),Y", curr);
                            // eprintln!("(${:02x}) = {:04x}", curr, self.bus.read_u16(curr as u16));
                            self.accumulator.0 = self
                                .bus
                                .read(self.bus.read_u16(curr as u16) + self.y.0 as u16);
                        }
                        AddressingMode::Relative => todo!(),
                        AddressingMode::ZeroPage => todo!(),
                        AddressingMode::ZeroPageX => todo!(),
                        AddressingMode::ZeroPageY => todo!(),
                    }
                    self.update_neg(self.accumulator.0);
                    self.update_zero(self.accumulator.0);
                }
                Operation::LDX => {
                    match inst.addressing_mode {
                        AddressingMode::Accumulator => todo!(),
                        AddressingMode::Absolute => todo!(),
                        AddressingMode::AbsoluteX => todo!(),
                        AddressingMode::AbsoluteY => todo!(),
                        AddressingMode::Immediate => {
                            self.x.0 = self.read_curr();
                        }
                        AddressingMode::Implied => todo!(),
                        AddressingMode::Indirect => todo!(),
                        AddressingMode::IndirectX => todo!(),
                        AddressingMode::IndirectY => todo!(),
                        AddressingMode::Relative => todo!(),
                        AddressingMode::ZeroPage => todo!(),
                        AddressingMode::ZeroPageX => todo!(),
                        AddressingMode::ZeroPageY => todo!(),
                    }
                    self.update_neg(self.x.0);
                    self.update_zero(self.x.0);
                }
                Operation::LDY => {
                    match inst.addressing_mode {
                        AddressingMode::Accumulator => todo!(),
                        AddressingMode::Absolute => todo!(),
                        AddressingMode::AbsoluteX => todo!(),
                        AddressingMode::AbsoluteY => todo!(),
                        AddressingMode::Immediate => {
                            self.y.0 = self.read_curr();
                        }
                        AddressingMode::Implied => todo!(),
                        AddressingMode::Indirect => todo!(),
                        AddressingMode::IndirectX => todo!(),
                        AddressingMode::IndirectY => todo!(),
                        AddressingMode::Relative => todo!(),
                        AddressingMode::ZeroPage => todo!(),
                        AddressingMode::ZeroPageX => todo!(),
                        AddressingMode::ZeroPageY => todo!(),
                    }
                    self.update_neg(self.y.0);
                    self.update_zero(self.y.0);
                }
                Operation::LSR => todo!("Instruction NYI: {}", inst),
                Operation::NOP => {}
                Operation::ORA => todo!("Instruction NYI: {}", inst),
                Operation::PHA => todo!("Instruction NYI: {}", inst),
                Operation::PHP => todo!("Instruction NYI: {}", inst),
                Operation::PLA => todo!("Instruction NYI: {}", inst),
                Operation::PLP => todo!("Instruction NYI: {}", inst),
                Operation::ROL => match inst.addressing_mode {
                    AddressingMode::Accumulator => {
                        let carry = self.status.intersects(Status::CARRY);
                        // eprintln!("self.status = {:?}", self.status);
                        self.status
                            .set(Status::CARRY, self.accumulator.0 & (1 << 7) != 0);
                        // eprintln!("self.status = {:?}", self.status);
                        self.accumulator.0 = (self.accumulator.0 << 1) | (carry as u8);
                    }
                    AddressingMode::Absolute => todo!(),
                    AddressingMode::AbsoluteX => todo!(),
                    AddressingMode::AbsoluteY => todo!(),
                    AddressingMode::Immediate => todo!(),
                    AddressingMode::Implied => todo!(),
                    AddressingMode::Indirect => todo!(),
                    AddressingMode::IndirectX => todo!(),
                    AddressingMode::IndirectY => todo!(),
                    AddressingMode::Relative => todo!(),
                    AddressingMode::ZeroPage => todo!(),
                    AddressingMode::ZeroPageX => todo!(),
                    AddressingMode::ZeroPageY => todo!(),
                },
                Operation::ROR => match inst.addressing_mode {
                    AddressingMode::Accumulator => {
                        let carry = self.status.intersects(Status::CARRY);
                        self.status.set(Status::CARRY, self.accumulator.0 & 1 != 0);
                        self.accumulator.0 = ((carry as u8) << 7) | (self.accumulator.0 >> 1);
                    }
                    AddressingMode::Absolute => todo!(),
                    AddressingMode::AbsoluteX => todo!(),
                    AddressingMode::AbsoluteY => todo!(),
                    AddressingMode::Immediate => todo!(),
                    AddressingMode::Implied => todo!(),
                    AddressingMode::Indirect => todo!(),
                    AddressingMode::IndirectX => todo!(),
                    AddressingMode::IndirectY => todo!(),
                    AddressingMode::Relative => todo!(),
                    AddressingMode::ZeroPage => todo!(),
                    AddressingMode::ZeroPageX => todo!(),
                    AddressingMode::ZeroPageY => todo!(),
                },
                Operation::RTI => todo!("Instruction NYI: {}", inst),
                Operation::RTS => {
                    self.pc = u16::from_le_bytes(self.pop_stack());
                }
                Operation::SBC => todo!("Instruction NYI: {}", inst),
                Operation::SEC => match inst.addressing_mode {
                    AddressingMode::Implied => {
                        self.status.set(Status::CARRY, true);
                    }
                    _ => unreachable!(),
                },
                Operation::SED => match inst.addressing_mode {
                    AddressingMode::Implied => {
                        self.status.set(Status::DECIMAL, true);
                    }
                    _ => unreachable!(),
                },
                Operation::SEI => match inst.addressing_mode {
                    AddressingMode::Implied => {
                        self.status.set(Status::IRQB_DISABLE, true);
                    }
                    _ => unreachable!(),
                },
                Operation::STA => match inst.addressing_mode {
                    AddressingMode::Accumulator => todo!(),
                    AddressingMode::Absolute => {
                        let pos = self.read_curr_u16();
                        self.bus.write(pos, self.accumulator.0);
                    }
                    AddressingMode::AbsoluteX => todo!(),
                    AddressingMode::AbsoluteY => todo!(),
                    AddressingMode::Immediate => todo!(),
                    AddressingMode::Implied => todo!(),
                    AddressingMode::Indirect => todo!(),
                    AddressingMode::IndirectX => todo!(),
                    AddressingMode::IndirectY => {
                        let ll = self.read_curr();
                        self.bus
                            .write((Wrapping(ll) + self.x).0 as u16, self.accumulator.0);
                    }
                    AddressingMode::Relative => todo!(),
                    AddressingMode::ZeroPage => {
                        let pos = self.read_curr();
                        self.bus.write(pos as u16, self.accumulator.0);
                    }
                    AddressingMode::ZeroPageX => todo!(),
                    AddressingMode::ZeroPageY => todo!(),
                },
                Operation::STX => match inst.addressing_mode {
                    AddressingMode::Accumulator => todo!(),
                    AddressingMode::Absolute => {
                        let pos = self.read_curr_u16();
                        self.bus.write(pos, self.x.0);
                    }
                    AddressingMode::AbsoluteX => todo!(),
                    AddressingMode::AbsoluteY => todo!(),
                    AddressingMode::Immediate => todo!(),
                    AddressingMode::Implied => todo!(),
                    AddressingMode::Indirect => todo!(),
                    AddressingMode::IndirectX => todo!(),
                    AddressingMode::IndirectY => todo!(),
                    AddressingMode::Relative => todo!(),
                    AddressingMode::ZeroPage => {
                        let pos = self.read_curr();
                        self.bus.write(pos as u16, self.x.0);
                    }
                    AddressingMode::ZeroPageX => todo!(),
                    AddressingMode::ZeroPageY => todo!(),
                },
                Operation::STY => todo!("Instruction NYI: {}", inst),
                Operation::TAX => todo!("Instruction NYI: {}", inst),
                Operation::TAY => match inst.addressing_mode {
                    AddressingMode::Implied => self.y = self.accumulator,
                    _ => unreachable!(),
                },
                Operation::TSX => todo!("Instruction NYI: {}", inst),
                Operation::TXA => match inst.addressing_mode {
                    AddressingMode::Implied => self.accumulator = self.x,
                    _ => unreachable!(),
                },
                Operation::TXS => {
                    self.stack_pointer = self.x.0;
                }
                Operation::TYA => todo!("Instruction NYI: {}", inst),
            }
            // eprintln!("     a = {:5} = 0x  {0:02x}", self.accumulator);
            // eprintln!("     x = {:5} = 0x  {0:02x}", self.x);
            // eprintln!("     y = {:5} = 0x  {0:02x}", self.y);
            // eprintln!("    sp = {:5} = 0x  {0:02x}", self.stack_pointer);
            // eprintln!("    pc = {:5} = 0x{0:04x}", self.pc);
            // let mut zpg8 = [0u8; 8];
            // for i in 0..8 {
            //     zpg8[i] = self.bus.read(i as u16);
            // }
            // eprintln!("   zpg[..8] = {:02x?}", zpg8);
            // std::thread::sleep(std::time::Duration::from_millis(5));
        }
        eprintln!("\nStopped because BRK set.");
        Ok(())
    }
}

const ROM_SIZE: usize = 32 * 1024;
type RomInner = [u8; ROM_SIZE];

#[derive(Copy, Clone, Debug)]
pub struct ROM {
    data: RomInner,
}

impl Deref for ROM {
    type Target = RomInner;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

fn main() -> anyhow::Result<()> {
    let file = std::env::args().nth(1).context("Usage: sfot <file>")?;
    let mut file = fs::File::open(file)?;
    let mut buf = [0; ROM_SIZE];
    file.read_exact(&mut buf)?;

    assert!(file.bytes().next().is_none());

    let bus = MyBus {
        ram: [0; 32 * 1024],
        rom: ROM { data: buf },
    };
    let mut s = MOS6502::new(bus);

    s.run()?;

    // dbg!(s);
    Ok(())
}
