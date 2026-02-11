{$X+}
UNIT DIS;
INTERFACE

function dis86(code: PChar; ofs: Word; var outStr: string): Word;
function WriteDisAsm86(code: PChar; ofs: Word) : word;

IMPLEMENTATION

const
  HexDigits: array[0..15] of Char = '0123456789ABCDEF';
  Reg8:  array[0..7] of string[2] = ('AL','CL','DL','BL','AH','CH','DH','BH');
  Reg16: array[0..7] of string[2] = ('AX','CX','DX','BX','SP','BP','SI','DI');
  SegReg: array[0..3] of string[2] = ('ES','CS','SS','DS');
  RMStr: array[0..7] of string[5] = ('BX+SI','BX+DI','BP+SI','BP+DI','SI','DI','BP','BX');
  Grp1: array[0..7] of string[3] = ('ADD','OR ','ADC','SBB','AND','SUB','XOR','CMP');
  Grp2: array[0..7] of string[3] = ('ROL','ROR','RCL','RCR','SHL','SHR','SAL','SAR');
  Grp3: array[0..7] of string[4] = ('TEST','TEST','NOT ','NEG ','MUL ','IMUL','DIV ','IDIV');
  Grp4: array[0..1] of string[3] = ('INC','DEC');
  Grp5: array[0..6] of string[4] = ('INC ','DEC ','CALL','CALL','JMP ','JMP ','PUSH');
  Jcc: array[0..15] of string[3] = ('JO ','JNO','JB ','JNB','JZ ','JNZ'
  ,'JBE','JA ','JS ','JNS','JP ','JNP','JL ','JGE','JLE','JG ');

function ByteHex(B: Byte): string;
begin
  ByteHex := HexDigits[B shr 4] + HexDigits[B and $0F];
end;

function WordHex(W: Word): string;
begin
  WordHex := ByteHex(Hi(W)) + ByteHex(Lo(W));
end;

function dis86(code: PChar; ofs: Word; var outStr: string): Word;
var
  IP, StartIP: Word;
  Op, ModRM: Byte;
  Mn, D, S, T, Pfx: string;
  TmpW: Word;
  TmpI: Integer;
  IsPrefix: Boolean;
  Gx: Byte;

  function GetB: Byte;
  begin
    GetB := Byte(code[IP]);
    Inc(IP);
  end;

  function GetW: Word;
  var L, H: Byte;
  begin
    L := GetB; H := GetB;
    GetW := L + (H shl 8);
  end;

  function SgnExt(B: Byte): Integer;
  begin
    if B >= 128 then SgnExt := Integer(B) - 256
    else SgnExt := B;
  end;

  procedure GetModRM(W: Boolean; var R, M: string);
  var
    Md, Rg, Rm: Byte;
    D8: Integer;
    D16: Word;
    Sign: string;
  begin
    ModRM := GetB;
    Md := (ModRM shr 6) and 3;
    Rg := (ModRM shr 3) and 7;
    Rm := ModRM and 7;

    if W then R := Reg16[Rg] else R := Reg8[Rg];

    if Md = 3 then
    begin
      if W then M := Reg16[Rm] else M := Reg8[Rm];
    end
    else
    begin
      M := '[';
      if (Md = 0) and (Rm = 6) then
      begin
        D16 := GetW;
        M := M + WordHex(D16) + 'h';
      end
      else
      begin
        M := M + RMStr[Rm];
        if Md = 1 then
        begin
          D8 := SgnExt(GetB);
          if D8 >= 0 then Sign := '+' + ByteHex(D8)
          else Sign := '-' + ByteHex(Abs(D8));
          M := M + Sign + 'h';
        end
        else if Md = 2 then
        begin
          D16 := GetW;
          M := M + '+' + WordHex(D16) + 'h';
        end;
      end;
      M := M + ']';
    end;
  end;

begin
  IP := ofs;
  StartIP := IP;
  Mn := ''; D := ''; S := ''; T := ''; Pfx := '';

  Repeat
    Op := GetB;
    IsPrefix := True;
    case Op of
      $26: Pfx := Pfx + 'ES: ';
      $2E: Pfx := Pfx + 'CS: ';
      $36: Pfx := Pfx + 'SS: ';
      $3E: Pfx := Pfx + 'DS: ';
      $F0: Pfx := Pfx + 'LOCK ';
      $F2: Pfx := Pfx + 'REPNE ';
      $F3: Pfx := Pfx + 'REP/REPE ';
      else IsPrefix := False;
    end;
  Until not IsPrefix;

  case Op of
    $00..$03: begin Mn:=Grp1[0]; GetModRM(Op and 1 <> 0, S, D); if Op<2 then begin T:=D; D:=S; S:=T; end; end;
    $08..$0B: begin Mn:=Grp1[1]; GetModRM(Op and 1 <> 0, S, D); if Op<$A then begin T:=D; D:=S; S:=T; end; end;
    $10..$13: begin Mn:=Grp1[2]; GetModRM(Op and 1 <> 0, S, D); if Op<$12 then begin T:=D; D:=S; S:=T; end; end;
    $18..$1B: begin Mn:=Grp1[3]; GetModRM(Op and 1 <> 0, S, D); if Op<$1A then begin T:=D; D:=S; S:=T; end; end;
    $20..$23: begin Mn:=Grp1[4]; GetModRM(Op and 1 <> 0, S, D); if Op<$22 then begin T:=D; D:=S; S:=T; end; end;
    $28..$2B: begin Mn:=Grp1[5]; GetModRM(Op and 1 <> 0, S, D); if Op<$2A then begin T:=D; D:=S; S:=T; end; end;
    $30..$33: begin Mn:=Grp1[6]; GetModRM(Op and 1 <> 0, S, D); if Op<$32 then begin T:=D; D:=S; S:=T; end; end;
    $38..$3B: begin Mn:=Grp1[7]; GetModRM(Op and 1 <> 0, S, D); if Op<$3A then begin T:=D; D:=S; S:=T; end; end;

    $06: begin Mn:='PUSH'; D:='ES'; end;
    $07: begin Mn:='POP'; D:='ES'; end;
    $0E: begin Mn:='PUSH'; D:='CS'; end;
    $16: begin Mn:='PUSH'; D:='SS'; end;
    $17: begin Mn:='POP'; D:='SS'; end;
    $1E: begin Mn:='PUSH'; D:='DS'; end;
    $1F: begin Mn:='POP'; D:='DS'; end;

    $27: Mn:='DAA'; $2F: Mn:='DAS'; $37: Mn:='AAA'; $3F: Mn:='AAS';

    $40..$47: begin Mn:='INC'; D:=Reg16[Op-$40]; end;
    $48..$4F: begin Mn:='DEC'; D:=Reg16[Op-$48]; end;

    $50..$57: begin Mn:='PUSH'; D:=Reg16[Op-$50]; end;
    $58..$5F: begin Mn:='POP';  D:=Reg16[Op-$58]; end;

    $60: Mn:='PUSHA';
    $61: Mn:='POPA';
    $62: begin Mn:='BOUND'; GetModRM(True, D, S); end;
    $68: begin Mn:='PUSH'; D:=WordHex(GetW)+'h'; end;
    $69: begin Mn:='IMUL'; GetModRM(True, D, S); T:=WordHex(GetW)+'h'; S:=S+', '+T; end;
    $6A: begin Mn:='PUSH'; D:=ByteHex(GetB)+'h'; end;
    $6B: begin Mn:='IMUL'; GetModRM(True, D, S); T:=ByteHex(GetB)+'h'; S:=S+', '+T; end;
    $6C: Mn:='INSB';
    $6D: Mn:='INSW';
    $6E: Mn:='OUTSB';
    $6F: Mn:='OUTSW';

    $70..$7F:
      begin
        Mn := Jcc[Op - $70];
        TmpI := SgnExt(GetB);
        D := 'short ' + WordHex(IP + TmpI);
      end;

    $80..$83:
      begin
        TmpW := IP; GetModRM((Op=$81) or (Op=$83), T, D);
        Mn := Grp1[(ModRM shr 3) and 7];
        if (Op = $81) then S := WordHex(GetW) + 'h'
        else S := ByteHex(GetB) + 'h';
      end;

    $84: begin Mn:='TEST'; GetModRM(False, S, D); end;
    $85: begin Mn:='TEST'; GetModRM(True, S, D); end;
    $86: begin Mn:='XCHG'; GetModRM(False, S, D); end;
    $87: begin Mn:='XCHG'; GetModRM(True, S, D); end;

    $88: begin Mn:='MOV'; GetModRM(False, S, D); end;
    $89: begin Mn:='MOV'; GetModRM(True, S, D); end;
    $8A: begin Mn:='MOV'; GetModRM(False, D, S); end;
    $8B: begin Mn:='MOV'; GetModRM(True, D, S); end;
    $8C: begin Mn:='MOV'; GetModRM(True, D, S); D:=SegReg[(ModRM shr 3) and 3]; end;
    $8D: begin Mn:='LEA'; GetModRM(True, D, S); end;
    $8E: begin Mn:='MOV'; GetModRM(True, S, D); S:=SegReg[(ModRM shr 3) and 3]; end;
    $8F: begin Mn:='POP'; GetModRM(True, T, D); end;

    $90: Mn:='NOP';
    $91..$97: begin Mn:='XCHG'; D:='AX'; S:=Reg16[Op-$90]; end;
    $98: Mn:='CBW'; $99: Mn:='CWD';
    $9A: Mn:='CALL far';
    $9B: Mn:='WAIT';
    $9C: Mn:='PUSHF'; $9D: Mn:='POPF'; $9E: Mn:='SAHF'; $9F: Mn:='LAHF';

    $A0: begin Mn:='MOV'; D:='AL'; S:='['+WordHex(GetW)+'h]'; end;
    $A1: begin Mn:='MOV'; D:='AX'; S:='['+WordHex(GetW)+'h]'; end;
    $A2: begin Mn:='MOV'; D:='['+WordHex(GetW)+'h]'; S:='AL'; end;
    $A3: begin Mn:='MOV'; D:='['+WordHex(GetW)+'h]'; S:='AX'; end;
    $A4: Mn:='MOVSB'; $A5: Mn:='MOVSW'; $A6: Mn:='CMPSB'; $A7: Mn:='CMPSW';
    $A8: begin Mn:='TEST'; D:='AL'; S:=ByteHex(GetB)+'h'; end;
    $A9: begin Mn:='TEST'; D:='AX'; S:=WordHex(GetW)+'h'; end;
    $AA: Mn:='STOSB'; $AB: Mn:='STOSW'; $AC: Mn:='LODSB'; $AD: Mn:='LODSW';
    $AE: Mn:='SCASB'; $AF: Mn:='SCASW';

    $B0..$B7: begin Mn:='MOV'; D:=Reg8[Op-$B0]; S:=ByteHex(GetB)+'h'; end;
    $B8..$BF: begin Mn:='MOV'; D:=Reg16[Op-$B8]; S:=WordHex(GetW)+'h'; end;

    $C0, $C1:
      begin
        GetModRM((Op=$C1), T, D);
        Mn := Grp2[(ModRM shr 3) and 7];
        S := ByteHex(GetB) + 'h';
      end;
    $C2: begin Mn:='RET'; S:=WordHex(GetW)+'h'; end;
    $C3: Mn:='RET';
    $C4: begin Mn:='LES'; GetModRM(True, D, S); end;
    $C5: begin Mn:='LDS'; GetModRM(True, D, S); end;
    $C6: begin Mn:='MOV'; GetModRM(False, T, D); S:='byte '+ByteHex(GetB)+'h'; end;
    $C7: begin Mn:='MOV'; GetModRM(True, T, D); S:='word '+WordHex(GetW)+'h'; end;
    $C8: begin Mn:='ENTER'; D:=WordHex(GetW)+'h'; S:=ByteHex(GetB)+'h'; end;
    $C9: Mn:='LEAVE';
    $CD: begin Mn:='INT'; D:=ByteHex(GetB)+'h'; end;
    $CE: Mn:='INTO'; $CF: Mn:='IRET';

    $D0, $D2:
      begin
        GetModRM(False, T, D);
        Mn:=Grp2[(ModRM shr 3) and 7];
        if Op=$D0 then S:='1' else S:='CL';
      end;
    $D1, $D3:
      begin
        GetModRM(True, T, D);
        Mn:=Grp2[(ModRM shr 3) and 7];
        if Op=$D1 then S:='1' else S:='CL';
      end;
    $D4: begin Mn:='AAM'; GetB; end;
    $D5: begin Mn:='AAD'; GetB; end;
    $D6: Mn:='SALC'; $D7: Mn:='XLAT';

    $E0: begin Mn:='LOOPNE'; TmpI:=SgnExt(GetB); D:=WordHex(IP+TmpI); end;
    $E1: begin Mn:='LOOPE';  TmpI:=SgnExt(GetB); D:=WordHex(IP+TmpI); end;
    $E2: begin Mn:='LOOP';   TmpI:=SgnExt(GetB); D:=WordHex(IP+TmpI); end;
    $E3: begin Mn:='JCXZ';   TmpI:=SgnExt(GetB); D:=WordHex(IP+TmpI); end;
    $E4: begin Mn:='IN'; D:='AL'; S:=ByteHex(GetB)+'h'; end;
    $E5: begin Mn:='IN'; D:='AX'; S:=ByteHex(GetB)+'h'; end;
    $E6: begin Mn:='OUT'; D:=ByteHex(GetB)+'h'; S:='AL'; end;
    $E7: begin Mn:='OUT'; D:=ByteHex(GetB)+'h'; S:='AX'; end;
    $E8: begin Mn:='CALL'; TmpW:=GetW; D:=WordHex(IP+TmpW); end;
    $E9: begin Mn:='JMP'; TmpW:=GetW; D:=WordHex(IP+TmpW); end;
    $EA: begin Mn:='JMP far'; TmpW:=GetW; D:=WordHex(GetW)+':'+WordHex(TmpW); end;
    $EB: begin Mn:='JMP'; TmpI:=SgnExt(GetB); D:='short '+WordHex(IP+TmpI); end;
    $EC: begin Mn:='IN'; D:='AL'; S:='DX'; end;
    $ED: begin Mn:='IN'; D:='AX'; S:='DX'; end;
    $EE: begin Mn:='OUT'; D:='DX'; S:='AL'; end;
    $EF: begin Mn:='OUT'; D:='DX'; S:='AX'; end;

    $F0: Mn:='LOCK';
    $F2: Mn:='REPNE';
    $F3: Mn:='REP';
    $F4: Mn:='HLT'; $F5: Mn:='CMC';
    $F6:
      begin
        GetModRM(False, T, D);
        Gx:=(ModRM shr 3) and 7;
        Mn:=Grp3[Gx];
        if Gx < 2 then S:=ByteHex(GetB)+'h';
      end;
    $F7:
      begin
        GetModRM(True, T, D);
        Gx:=(ModRM shr 3) and 7;
        Mn:=Grp3[Gx];
        if Gx < 2 then S:=WordHex(GetW)+'h';
      end;
    $F8: Mn:='CLC'; $F9: Mn:='STC'; $FA: Mn:='CLI'; $FB: Mn:='STI'; $FC: Mn:='CLD'; $FD: Mn:='STD';

    $FE: begin GetModRM(False, T, D); Mn:=Grp4[(ModRM shr 3) and 1]; end;
    $FF:
      begin
        GetModRM(True, T, D);
        Gx := (ModRM shr 3) and 7;
        Mn := Grp5[Gx];
        if (Gx = 3) or (Gx = 5) then D := 'far ' + D;
      end;
    else Mn := 'DB ' + ByteHex(Op) + 'h';
  end;

  outStr := Pfx + Mn;
  if D <> '' then outStr := outStr + ' ' + D;
  if S <> '' then outStr := outStr + ', ' + S;

  dis86 := IP - StartIP;
end;

function WriteDisAsm86(code: PChar; ofs: Word) : word;
var     InstrLen : word;
        DisStr : string;
        i : integer;
begin

    InstrLen := dis86(code, ofs, DisStr);
    Write(WordHex(ofs), ':   ');

    for i := 0 to 3 do begin
      if i < InstrLen then Write(ByteHex(ord(code[ofs + i])), ' ')
      else Write('   ');
    end;

    Writeln(' ', DisStr);
    WriteDisAsm86 := InstrLen;
end;

end.

