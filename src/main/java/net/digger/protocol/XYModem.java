/**
 * Copyright © 2017  David Walton
 * 
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package net.digger.protocol;

import java.io.IOException;
import java.io.OutputStream;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import net.digger.util.crc.CRC;

/**
 * Implementation of client side of XModem and YModem protocols,
 * for downloading files.
 * <p>
 * Supports XModem-Checksum, XModem-CRC, XModem-1k, YModem-Batch, YModem-G.<br>
 * Implements just enough of ZModem to support AutoDownload, relying on sender
 * fallback to X/YModem.
 * <p>
 * Based on X/YMODEM Protocol Reference, June 18 1988:<br>
 * http://pauillac.inria.fr/~doligez/zmodem/ymodem.txt<br>
 * ZModem AutoDownload support from<br> 
 * The ZMODEM Inter Application File Transfer Protocol, Oct-14-88<br>
 * http://gallium.inria.fr/~doligez/zmodem/zmodem.txt<br>
 * with values defined from<br>
 * http://read.pudn.com/downloads/sourcecode/comm/984/ZMODEM.H__.htm
 * 
 * @author walton
 */
public class XYModem {
	// X/YModem characters
	private static final char SOH = 0x01;	// Start 128-byte block header
	private static final char STX = 0x02;	// Start 1024-byte block header
	private static final char EOT = 0x04;	// File transfer complete
	private static final char ACK = 0x06;	// Data received ok
	private static final char BS  = 0x08;	// Backspace
	private static final char NAK = 0x15;	// Error receiving data
	private static final char CAN = 0x18;	// Cancel download
	private static final char EOF = 0x1A;	// Padding for extra block space and File transfer complete (alternate)

	// ZModem characters
	private static final char CR  = 0x0D;	// Carriage return
	private static final char LF  = 0x0A;	// Line feed
	private static final char XON = 0x11;	// XON
	private static final char ZPAD = '*';	// Frame header start char
	private static final char ZDLE = 0x18;	// ZModem Data Link Escape character
//	private static final char ZDLEE = (ZDLE ^ 0x40);	// ZDLE escaped
//	private static final char ZBIN = 'A';	// Binary header type
	private static final char ZHEX = 'B';	// Hex header type
//	private static final char ZBIN32 = 'C';	// CRC32 binary header type
//	private static final char ZRQINIT = 0;	// Request ZRINIT

	// ZRQINIT frame: * * ZDLE B ZRQINIT ZF3 ZF2 ZF1 ZF0 CRC-1 CRC-2 CR LF XON
	private static final char[] ZRQINITFrame = new char[] {
		ZPAD, ZPAD, ZDLE, ZHEX,
		'0', '0',	// ZRQINIT
		'0', '0',	// ZF3
		'0', '0',	// ZF2
		'0', '0',	// ZF1
		'0', '0',	// ZF0
		'0', '0',	// CRC-1
		'0', '0',	// CRC-2
		CR, LF, XON
	};

	private final IOHandler io;
	private Character waitingData = null;
	private ProtocolDetector protocol;
	private Character handshake = null;
	private boolean block0Done = false;
	private int autoDownloadIndex = 0;
	
	public XYModem(IOHandler ioHandler) {
		this.io = ioHandler;
	}
	
	public boolean autoDownloadDetect(char ch) {
		/*
		 * Chapter 7.2  Link Escape Encoding
		 * ZMODEM achieves data transparency by extending the 8 bit character set
		 * (256 codes) with escape sequences based on the ZMODEM data link escape
		 * character ZDLE.
		 * This and other constants are defined in the zmodem.h include file.
		 * Please note that constants with a leading 0 are octal constants in C.
		 * If a ZDLE character appears in binary data, it is prefixed with
		 * ZDLE, then sent as ZDLEE.
		 * The value for ZDLE is octal 030 (ASCII CAN).
		 * The receiving program decodes any sequence of ZDLE followed by a byte with
		 * bit 6 set and bit 5 reset (upper case letter, either parity) to the
		 * equivalent control character by inverting bit 6.  This allows the
		 * transmitter to escape any control character that cannot be sent by the
		 * communications medium.  In addition, the receiver recognizes escapes for
		 * 0177 and 0377 should these characters need to be escaped.
		 * ZMODEM software escapes ZDLE, 020, 0220, 021, 0221, 023, and 0223.  If
		 * preceded by 0100 or 0300 (@), 015 and 0215 are also escaped to protect the
		 * Telenet command escape CR-@-CR.  The receiver ignores 021, 0221, 023, and
		 * 0223 characters in the data stream.
		 */
		/*
		 * Chapter 7.3  Header
		 * All ZMODEM frames begin with a header which may be sent in binary or HEX
		 * form.
		 * Either form of the header contains the same raw information:
		 *  + A type byte
		 *  + Four bytes of data indicating flags and/or numeric quantities depending
		 *    on the frame type
		 */
		/*
		 * Chapter 7.3.1  16 Bit CRC Binary Header
		 * A binary header begins with the sequence ZPAD, ZDLE, ZBIN.
		 * The frame type byte is ZDLE encoded.
		 * The four position/flags bytes are ZDLE encoded.
		 * A two byte CRC of the frame type and position/flag bytes is ZDLE encoded.
		 */
		/*
		 * Figure 2.  16 Bit CRC Binary Header
		 * 		* ZDLE A TYPE F3/P0 F2/P1 F1/P2 F0/P3 CRC-1 CRC-2
		 */
		/*
		 * Chapter 7.3.2  32 Bit CRC Binary Header
		 * A "32 bit CRC" Binary header is similar to a Binary Header, except the
		 * ZBIN (A) character is replaced by a ZBIN32 (C) character, and four
		 * characters of CRC are sent.
		 */
		/*
		 * Figure 3.  32 Bit CRC Binary Header
		 * 		* ZDLE C TYPE F3/P0 F2/P1 F1/P2 F0/P3 CRC-1 CRC-2 CRC-3 CRC-4
		 */
		/*
		 * Chapter 7.3.3  HEX Header
		 * The sender also uses hex
		 * headers when they are not followed by binary data subpackets.
		 * A hex header begins with the sequence ZPAD, ZPAD, ZDLE, ZHEX.
		 * The type byte, the four position/flag bytes, and the 16 bit CRC thereof
		 * are sent in hex using the character set 01234567890abcdef.  Upper case hex
		 * digits are not allowed; they false trigger XMODEM and YMODEM programs.
		 * A carriage return and line feed are sent with HEX headers.  The receive
		 * routine expects to see at least one of these characters, two if the first
		 * is CR.
		 * An XON character is appended to all HEX packets except ZACK and ZFIN.
		 */
		/*
		 * Figure 4.  HEX Header
		 * 		* * ZDLE B TYPE F3/P0 F2/P1 F1/P2 F0/P3 CRC-1 CRC-2 CR LF XON
		 * (TYPE, F3...F0, CRC-1, and CRC-2 are each sent as two hex digits.)
		 */
		/*
		 * Chapter 8.1  Session Startup
		 * To start a ZMODEM file transfer session, the sending program is called
		 * with the names of the desired file(s) and option(s).
		 * The sending program may send the string "rz\r" to invoke the receiving
		 * program from a possible command mode.  The "rz" followed by carriage
		 * return activates a ZMODEM receive program or command if it were not
		 * already active.
		 * The sender may then display a message intended for human consumption, such
		 * as a list of the files requested, etc.
		 * Then the sender may send a ZRQINIT header.  The ZRQINIT header causes a
		 * previously started receive program to send its ZRINIT header without
		 * delay.
		 * In an interactive or conversational mode, the receiving application may
		 * monitor the data stream for ZDLE.  The following characters may be scanned
		 * for B00 indicating a ZRQINIT header, a command to download a command or
		 * data.
		 * The sending program awaits a command from the receiving program to start
		 * file transfers.  If a "C", "G", or NAK is received, an XMODEM or YMODEM
		 * file transfer is indicated, and file transfer(s) use the YMODEM protocol.
		 * Note: With ZMODEM and YMODEM, the sending program provides the file name,
		 * but not with XMODEM.
		 */
		/*
		 * Chapter 8.1  Session Startup
		 * In an interactive or conversational mode, the receiving	application may
		 * monitor	the data stream	for ZDLE.  The following characters may	be scanned
		 * for B00	indicating a ZRQINIT header, a command to download a command or
		 * data.
		 * [This indicates, though not explicitly stated, that ZRQINIT is always sent
		 * with a HEX header.]
		 */
		/*
		 * Chapter 11.1  ZRQINIT
		 * Sent by the sending program, to trigger the receiving program to send
		 * its ZRINIT header.  This avoids the aggravating startup delay
		 * associated with XMODEM and Kermit transfers.  The sending program may
		 * repeat the receive invitation (including ZRQINIT) if a response is
		 * not obtained at first.
		 * ZF0 contains ZCOMMAND if the program is attempting to send a command,
		 * 0 otherwise.
		 */
		if (ch == ZRQINITFrame[autoDownloadIndex]) {
			autoDownloadIndex++;
			if (autoDownloadIndex == ZRQINITFrame.length) {
				autoDownloadIndex = 0;
				return true;
			}
		} else {
			autoDownloadIndex = 0;
		}
		return false;
	}
	
	public void download() {
		protocol = new ProtocolDetector(io);
		try {
			while (true) {
				block0Done = false;
				if (!sendHandshake()) {
					cancel("Handshake timed out.");
					return;
				}
				if (!downloadFile()) {
					break;
				}
				/*
				 * Chapter 5.  YMODEM Batch File Transmission
				 * After the file contents and XMODEM EOT have been transmitted and
				 * acknowledged, the receiver again asks for the next pathname.
				 */
			}
		} catch (UserCancelException e) {
			cancel("Download cancelled by user.");
		} catch (IOException e) {
			/*
			 * Chapter 5.  YMODEM Batch File Transmission
			 * If the file cannot be
			 * opened for writing, the receiver cancels the transfer with CAN characters
			 * as described above.
			 */
			cancel("Error writing file.  Download cancelled.");
		}
	}
	
	/**
	 * Send handshake and wait for response.
	 * 
	 * @return True if response arrived, false if timed out.
	 * @throws UserCancelException If user cancelled the download.
	 */
	private boolean sendHandshake() throws UserCancelException {
		// wait until nothing coming in
		purge();
		/*
		 * Chapter 7.3.2  Receive_Program_Considerations
		 * The receiver has a 10-second timeout.  It sends a <nak> every time it
		 * times out.  The receiver's first timeout, which sends a <nak>, signals the
		 * transmitter to start.  Optionally, the receiver could send a <nak>
		 * immediately, in case the sender was ready.  This would save the initial 10
		 * second timeout.  However, the receiver MUST continue to timeout every 10
		 * seconds in case the sender wasn't ready.
		 */
		if (handshake != null) {
			/*
			 * Chapter 7.3.1  Common_to_Both_Sender_and_Receiver
			 * All errors are retried 10 times.
			 */
			return retry(10, () -> {
				io.write(handshake);
				return waitForData(10000);
			});
		}
		/*
		 * Chapter 6.  YMODEM-g File Transmission
		 * The g option is driven by the receiver, which initiates the batch transfer
		 * by transmitting a G instead of C.
		 * The sender expects an inital G to initiate the transmission of a
		 * particular file, and also expects an ACK on the EOT sent at the end of
		 * each file.
		 */
		// try 'G' a few times
		io.log("Checking for YModem-G...");
		if (retry(3, () -> {
			io.write('G');
			return waitForData(2000);
		})) {
// here we will know if streaming ==> YModem-G
			protocol.setStreaming(true);
			handshake = 'G';
			return true;
		}
		protocol.setStreaming(false);
		/*
		 * Chapter 4.2  CRC-16 Option
		 * The XMODEM/CRC protocol is similar to the XMODEM protocol, except that the
		 * receiver specifies CRC-16 by sending C (Hex 43) instead of NAK when
		 * requesting the FIRST block.
		 */
		/*
		 * Chapter 8.2.1  Common_to_Both_Sender_and_Receiver
		 * A receiving
		 * program that wishes to receive in CRC mode implements the mode setting
		 * handshake by sending a <C> in place of the initial <nak>.  If the sending
		 * program supports CRC mode it will recognize the <C> and will set itself
		 * into CRC mode, and respond by sending the first block as if a <nak> had
		 * been received. If the sending program does not support CRC mode it will
		 * not respond to the <C> at all. After the receiver has sent the <C> it will
		 * wait up to 3 seconds for the <soh> that starts the first block. If it
		 * receives a <soh> within 3 seconds it will assume the sender supports CRC
		 * mode and will proceed with the file exchange in CRC mode. If no <soh> is
		 * received within 3 seconds the receiver will switch to checksum mode, send
		 * a <nak>, and proceed in checksum mode. If the receiver wishes to use
		 * checksum mode it should send an initial <nak> and the sending program
		 * should respond to the <nak> as defined in the original Modem Protocol.
		 * After the mode has been set by the initial <C> or <nak> the protocol
		 * follows the original Modem Protocol and is identical whether the checksum
		 * or CRC is being used.
		 */
		/*
		 * Chapter 8.2.2  Receive_Program_Considerations
		 * 1.  the initial <C> can be garbled or lost.
		 * 2.  the initial <soh> can be garbled.
		 * The first problem can be solved if the receiver sends a second <C> after
		 * it times out the first time. This process can be repeated several times.
		 * It must not be repeated too many times before sending a <nak> and
		 * switching to checksum mode or a sending program without CRC support may
		 * time out and abort. Repeating the <C> will also fix the second problem if
		 * the sending program cooperates by responding as if a <nak> were received
		 * instead of ignoring the extra <C>.
		 */
		// try 'C' a few times
		io.log("Checking for YModem-Batch, XModem-1K or XModem-CRC...");
		if (retry(3, () -> {
			io.write('C');
			return waitForData(2000);
		})) {
// here we know if CRC ==> XModem-CRC, XModem-1K, YModem-Batch
			protocol.setCRC(true);
			handshake = 'C';
			return true;
		}
		protocol.setCRC(false);
		io.log("Starting XModem-Checksum...");
		// try NAK a few times
		if (retry(4, () -> {
			io.write(NAK);
			return waitForData(2000);
		})) {
// here we know if Checksum ==> XModem-Checksum
			handshake = NAK;
			return true;
		}
		return false;
	}

	/**
	 * Download a file.
	 * 
	 * @return True if session can continue, false to end session.
	 * @throws UserCancelException If user cancelled the download.
	 * @throws IOException 
	 */
	private boolean downloadFile() throws UserCancelException, IOException {
		/*
		 * Chapter 7.2  Transmission Medium Level Protocol
		 * Each block of the transfer looks like:
		 * 		<SOH><blk #><255-blk #><--128 data bytes--><cksum>
		 */
		boolean endOfFile = false;
		Character lastBlockNum = null;
		Download download = null;
		OutputStream os = null;
		int count = 0;
		try {
			while (true) {
				/*
				 * Chapter 7.3.1  Common_to_Both_Sender_and_Receiver
				 * All errors are retried 10 times.
				 * [We choose to interpret that as each block is attempted 10 times, regardless of the specific error.]
				 */
				int retries;
				for (retries=0; retries<10; retries++) {
					byte[] header = readHeader();
					if (header == null) {
						/*
						 * Chapter 6.  YMODEM-g File Transmission
						 * If an error is detected in a YMODEM-g transfer, the receiver aborts the
						 * transfer with the multiple CAN abort sequence.
						 */
						if (protocol.isStreaming) {
							cancel("Timed out waiting for block header.  Download aborted.");
							return false;
						}
System.out.println("NAK: Block header timeout.");
						nak();
						continue;	// retry the block
					}
					if ((header[0] == EOT) || (header[0] == EOF)) {
						/*
						 * Chapter 6.  YMODEM-g File Transmission
						 * If an error is detected in a YMODEM-g transfer, the receiver aborts the
						 * transfer with the multiple CAN abort sequence.
						 * [In other words, NAK is not used.]
						 */
						if (!endOfFile && !protocol.isStreaming) {
							// make them send EOT twice, to make sure not glitched data
							endOfFile = true;
System.out.println("NAK: Doublecheck EOT.");
							nak();
							continue;	// retry the block
						}
						os.close();
						try {
							download.resetLastModified();
						} catch (IOException e) {
							// just ignore the error
						}
						io.log("Download complete.");
						io.received(download);
						// reset the per-file vars, in case another file coming
						endOfFile = false;
						lastBlockNum = null;
						download = null;
						os = null;
						count = 0;
						/*
						 * Chapter 2.  YMODEM MINIMUM REQUIREMENTS
						 * At the end of each file, the sending program shall send EOT up to ten
						 * times until it receives an ACK character.
						 */
						/*
						 * Chapter 6.  YMODEM-g File Transmission
						 * The sender expects an inital G to initiate the transmission of a
						 * particular file, and also expects an ACK on the EOT sent at the end of
						 * each file.
						 */
						io.write(ACK);
						return protocol.isBatch;
					}
					int packetSize;
					/*
					 * Chapter 2.  YMODEM MINIMUM REQUIREMENTS
					 * The receiving program must accept any mixture of 128 and 1024 byte
					 * blocks within each file it receives.  Sending programs may
					 * arbitrarily switch between 1024 and 128 byte blocks.
					 */
					/*
					 * Chapter 4.3  XMODEM-1k 1024 Byte Block
					 * An STX (02) replaces the SOH (01) at the beginning of the transmitted
					 * block to notify the receiver of the longer block length.  The transmitted
					 * block contains 1024 bytes of data.  The receiver should be able to accept
					 * any mixture of 128 and 1024 byte blocks.
					 */
					switch (header[0]) {
						case SOH:	// 128-byte packets. XModem, XModem-CRC, XModem-1K, YModem-Batch
// here (block 1) we know if 128 ==> XModem, XModem-CRC, XModem-1K, YModem-Batch
							packetSize = 128;
							break;
						case STX:	// 1024-byte packets. XModem-1K, YModem-Batch
// here (block 1) we know if 1K ==> XModem-1K, YModem-Batch
							packetSize = 1024;
							break;
						default:
							/*
							 * Chapter 6.  YMODEM-g File Transmission
							 * If an error is detected in a YMODEM-g transfer, the receiver aborts the
							 * transfer with the multiple CAN abort sequence.
							 */
							if (protocol.isStreaming) {
								cancel("Invalid packet header (0x" + Integer.toHexString(header[0]) + ").  Download aborted.");
								return false;
							}
System.out.println("NAK: Invalid packet header 0x" + Integer.toHexString(header[0]) + ".");
							nak();
							continue;	// retry the block
					}
					char blockNum = (char)(header[1] & 0xFF);
					if ((header[2] & 0xFF) != (255 - blockNum)) {
						/*
						 * Chapter 6.  YMODEM-g File Transmission
						 * If an error is detected in a YMODEM-g transfer, the receiver aborts the
						 * transfer with the multiple CAN abort sequence.
						 */
						if (protocol.isStreaming) {
							cancel("Invalid block number.  Download aborted.");
							return false;
						}
System.out.println("NAK: Invalid block number " + blockNum + ".");
						nak();
						continue;	// retry the block
					}
					/*
					 * Chapter 7.3.2  Receive_Program_Considerations
					 * If a valid block number is received, it will be: 1) the
					 * expected one, in which case everything is fine; or 2) a repeat of the
					 * previously received block.  This should be considered OK, and only
					 * indicates that the receivers <ack> got glitched, and the sender re-
					 * transmitted; 3) any other block number indicates a fatal loss of
					 * synchronization, such as the rare case of the sender getting a line-glitch
					 * that looked like an <ack>.  Abort the transmission, sending a <can>
					 */
					if (((lastBlockNum == null) && (blockNum > 1)) 
							|| ((lastBlockNum != null) && (blockNum != lastBlockNum) && (blockNum != (lastBlockNum + 1)))) {
						cancel("Out of sequence block number.  Download aborted.");
						return false;
					}
					byte[] packet = readPacket(packetSize);
					if (packet == null) {
						/*
						 * Chapter 6.  YMODEM-g File Transmission
						 * If an error is detected in a YMODEM-g transfer, the receiver aborts the
						 * transfer with the multiple CAN abort sequence.
						 */
						if (protocol.isStreaming) {
							cancel("Timed out waiting for block data.  Download aborted.");
							return false;
						}
System.out.println("NAK: Block data timeout.");
						nak();
						continue;	// retry the block
					}
					boolean valid = false;
					if (protocol.isCRC) {
						/*
						 * Chapter 4.2  CRC-16 Option
						 * A two byte CRC is sent in place of the one
						 * byte arithmetic checksum.
						 */
						/*
						 * Chapter 8.  XMODEM/CRC Overview
						 * Each block of the transfer in CRC mode looks like:
						 * 		<SOH><blk #><255-blk #><--128 data bytes--><CRC hi><CRC lo>
						 */
						Character ch = readData(1000);
System.out.print("{"+ch+"0x"+Integer.toHexString(ch)+"}");
						if (ch == null) {
							if (protocol.isStreaming) {
								cancel("Timed out waiting for CRC.  Download aborted.");
								return false;
							}
System.out.println("NAK: Block CRC timeout.");
							nak();
							continue;	// retry the block
						}
						Character ch2 = readData(1000);
System.out.print("{"+ch2+"0x"+Integer.toHexString(ch2)+"}");
						if (ch2 == null) {
							if (protocol.isStreaming) {
								cancel("Timed out waiting for CRC.  Download aborted.");
								return false;
							}
System.out.println("NAK: Block CRC timeout.");
							nak();
							continue;	// retry the block
						}
						char crc = (char)((ch << 8) + ch2);
						valid = (crc == CRC.calculate(CRC.CRC16_CCITT_XModem, packet));
System.out.println("Expected CRC 0x" + Integer.toHexString(crc) + ", got 0x" + Long.toHexString(CRC.calculate(CRC.CRC16_CCITT_XModem, packet)));
					} else {
						/*
						 * Chapter 7.2  Transmission Medium Level Protocol
						 * Each block of the transfer looks like:
						 * 		<SOH><blk #><255-blk #><--128 data bytes--><cksum>
						 */
						Character ch = readData(1000);
						if (ch == null) {
							if (protocol.isStreaming) {
								cancel("Timed out waiting for checksum.  Download aborted.");
								return false;
							}
System.out.println("NAK: Block checksum timeout.");
							nak();
							continue;	// retry the block
						}
						long checksum = CRC.calculate(CRC.Checksum8, packet);
System.out.println("Expected checksum 0x" + Integer.toHexString(ch) + ", got 0x" + Long.toHexString(checksum));
						valid = (ch == checksum);
					}
					if (!valid) {
						/*
						 * Chapter 6.  YMODEM-g File Transmission
						 * If an error is detected in a YMODEM-g transfer, the receiver aborts the
						 * transfer with the multiple CAN abort sequence.
						 */
						if (protocol.isStreaming) {
							cancel("Invalid block CRC.  Download aborted.");
							return false;
						}
						/*
						 * Chapter 5.  YMODEM Batch File Transmission
						 * If the filename block is received with a CRC or other error, a
						 * retransmission is requested.
						 */
System.out.println("NAK: Invalid CRC/checksum.");
						nak();
						continue;	// retry the block
					}
					/*
					 * Chapter 7.3.2  Receive_Program_Considerations
					 * If a valid block number is received, it will be: 1) the
					 * expected one, in which case everything is fine; or 2) a repeat of the
					 * previously received block.  This should be considered OK, and only
					 * indicates that the receivers <ack> got glitched, and the sender re-
					 * transmitted; [...].
					 */
					// only process the block if it's not a repeat
					if ((lastBlockNum == null) || (blockNum != lastBlockNum)) {
						if (blockNum == 0) {
// here we know if batch (block 0) ==> YModem-Batch
							if (!block0Done) {
								protocol.setBatch(true);
								download = processBlock0(packet);
								/*
								 * Chapter 2.  YMODEM MINIMUM REQUIREMENTS
								 * The end of a transfer session shall be signified by a null (empty)
								 * pathname, this pathname block shall be acknowledged the same as other
								 * pathname blocks.
								 */
								/*
								 * Chapter 5.  YMODEM Batch File Transmission
								 * Transmission of a null pathname terminates batch file transmission.
								 * Note that transmission of no files is not necessarily an error.  This is
								 * possible if none of the files requested of the sender could be opened for
								 * reading.
								 */
								if (download == null) {
									io.log("No more files to download.");
									/*
									 * Chapter 6.  YMODEM-g File Transmission
									 * When the sender recognizes the G, it
									 * bypasses the usual wait for an ACK to each transmitted block, sending
									 * succeeding blocks at full speed, subject to XOFF/XON or other flow control
									 * exerted by the medium.
									 */
									if (!protocol.isStreaming) {
										io.write(ACK);
									}
									return false;
								}
								os = Files.newOutputStream(download.file);
								block0Done = true;
								lastBlockNum = blockNum;
								/*
								 * Chapter 2.  YMODEM MINIMUM REQUIREMENTS
								 * When the receiving program receives this block and successfully
								 * opened the output file, it shall acknowledge this block with an ACK
								 * character and then proceed with a normal XMODEM file transfer
								 * beginning with a "C" or NAK tranmsitted by the receiver.
								 */
								/*
								 * Chapter 5.  YMODEM Batch File Transmission
								 * After the filename block has been received,
								 * it is ACK'ed if the write open is successful.
								 * The receiver then initiates transfer of the file contents with a "C"
								 * character, according to the standard XMODEM/CRC protocol.
								 */
								/*
								 * Chapter 6.  YMODEM-g File Transmission
								 * When the sender recognizes the G, it
								 * bypasses the usual wait for an ACK to each transmitted block, sending
								 * succeeding blocks at full speed, subject to XOFF/XON or other flow control
								 * exerted by the medium.
								 * The sender expects an inital G to initiate the transmission of a
								 * particular file, and also expects an ACK on the EOT sent at the end of
								 * each file.
								 */
								if (!protocol.isStreaming) {
									io.write(ACK);
								}
								io.write(handshake);
								break;	// on to the next block (and file)
							}
						} else if (blockNum == 1) {
							if (!block0Done) {
								protocol.setBatch(false);
								download = new Download();
								os = Files.newOutputStream(download.file);
							}
							protocol.set1K(header[0] == STX);
						}
						if (download.length == 0) {
							os.write(packet);
							count += packet.length;
						} else {
							/*
							 * Chapter 5.  YMODEM Batch File Transmission
							 * The receiver stores the specified number of characters, discarding
							 * any padding added by the sender to fill up the last block.
							 */
							for (byte b : packet) {
								if (count >= download.length) {
									break;
								}
								os.write(b);
								count++;
							}
						}
						io.progress(count, download.length);
						lastBlockNum = blockNum;
					}
					/*
					 * Chapter 6.  YMODEM-g File Transmission
					 * When the sender recognizes the G, it
					 * bypasses the usual wait for an ACK to each transmitted block, sending
					 * succeeding blocks at full speed, subject to XOFF/XON or other flow control
					 * exerted by the medium.
					 */
					if (!protocol.isStreaming) {
						io.write(ACK);
					}
					break;	// on to the next block
				}	// end of retry loop
				if (retries >= 10) {
					cancel("Too many errors.  Download aborted.");
					return false;
				}
				// on to the next block
			}
		} finally {
			if (os != null) {
				os.close();
			}
			if (download != null) {
				Files.delete(download.file);
			}
		}
	}
	
	private byte[] readHeader() throws UserCancelException {
		/*
		 * Chapter 7.2  Transmission Medium Level Protocol
		 * Each block of the transfer looks like:
		 * 		<SOH><blk #><255-blk #><--128 data bytes--><cksum>
		 */
		byte[] header = new byte[3];
		Character ch;
		/*
		 * Chapter 7.3.2  Receive_Program_Considerations
		 * The receiver has a 10-second timeout.  It sends a <nak> every time it
		 * times out.
		 */
		/*
		 * Chapter 7.4  Programming Tips
		 * The character-receive subroutine should be called with a parameter
		 * specifying the number of seconds to wait.  The receiver should first
		 * call it with a time of 10, then <nak> and try again, 10 times.
		 */
		int timeout = 10000;
		ch = readData(timeout);
		if (ch == null) {
			return null;
		}
		header[0] = (byte)(ch & 0xFF);
		/*
		 * Chapter 7.3.2  Receive_Program_Considerations
		 * Once into a receiving a block, the receiver goes into a one-second timeout
		 * for each character and the checksum.
		 */
		/*
		 * Chapter 7.4  Programming Tips
		 * After receiving the <soh>, the receiver should call the character
		 * receive subroutine with a 1-second timeout, for the remainder of the
		 * message and the <cksum>.  Since they are sent as a continuous stream,
		 * timing out of this implies a serious like glitch that caused, say,
		 * 127 characters to be seen instead of 128.
		 */
		timeout = 1000;
		if ((ch == EOT) || (ch == EOF)) {
			return header;
		}
		/*
		 * Chapter 4.1  Graceful Abort
		 * The YAM and Professional-YAM X/YMODEM routines recognize a sequence of two
		 * consecutive CAN (Hex 18) characters without modem errors (overrun,
		 * framing, etc.) as a transfer abort command.  This sequence is recognized
		 * when is waiting for the beginning of a block [...].
		 */
		if (ch == CAN) {
			ch = readData(timeout);
			if ((ch == null) || (ch != CAN)) {
				return null;
			}
			header[1] = (byte)(ch & 0xFF);
			return header;
		}
		/*
		 * Chapter 4.3  XMODEM-1k 1024 Byte Block
		 * An STX (02) replaces the SOH (01) at the beginning of the transmitted
		 * block to notify the receiver of the longer block length.  The transmitted
		 * block contains 1024 bytes of data.  The receiver should be able to accept
		 * any mixture of 128 and 1024 byte blocks.
		 */
		if ((ch != SOH) && (ch != STX)) {
			return header;
		}
		ch = readData(timeout);
		if (ch == null) {
			return null;
		}
		header[1] = (byte)(ch & 0xFF);
		ch = readData(timeout);
		if (ch == null) {
			return null;
		}
		header[2] = (byte)(ch & 0xFF);
		return header;
	}
	
	private byte[] readPacket(int packetSize) throws UserCancelException {
		/*
		 * Chapter 7.4  Programming Tips
		 * After receiving the <soh>, the receiver should call the character
		 * receive subroutine with a 1-second timeout, for the remainder of the
		 * message and the <cksum>.  Since they are sent as a continuous stream,
		 * timing out of this implies a serious like glitch that caused, say,
		 * 127 characters to be seen instead of 128.
		 */
		byte[] packet = new byte[packetSize];
		for (int i=0; i<packetSize; i++) {
			Character ch = readData(1000);
			if (ch == null) {
				return null;
			}
			packet[i] = (byte)(ch & 0xFF);
		}
		return packet;
	}

	// read filename, size, etc from block 0
	private Download processBlock0(byte[] packet) throws IOException {
		// FILENAME
		/*
		 * Chapter 2.  YMODEM MINIMUM REQUIREMENTS
		 * The sending program shall send the pathname (file name) in block 0.
		 * The pathname shall be a null terminated ASCII string [...].
		 */
		/*
		 * Chapter 5.  YMODEM Batch File Transmission
		 * The pathname (conventionally, the file name) is sent as a null
		 * terminated ASCII string.
		 * No spaces are included in the pathname.
		 * If directories are included, they are delimited by /; i.e.,
		 * "subdir/foo" is acceptable, "subdir\foo" is not.
		 * Transmission of a null pathname terminates batch file transmission.
		 * Note that transmission of no files is not necessarily an error.  This is
		 * possible if none of the files requested of the sender could be opened for
		 * reading.
		 */
		if (packet[0] == 0x00) {
			return null;
		}
		int i = 0;
		String temp = "";
		while (i < packet.length) {
			byte b = packet[i];
			if (b == 0x00) {
				i++;
				break;
			}
			temp += (char)b;
			i++;
		}
		Download download = new Download(temp);
		if ((i >= packet.length) || (packet[i] == 0x00)) {
			return download;
		}

		// FILE SIZE
		/*
		 * Chapter 5.  YMODEM Batch File Transmission
		 * The file length and each of the succeeding fields are optional.
		 * Fields may not be skipped.
		 * The length field is stored in the block as a decimal string counting
		 * the number of data bytes in the file.  The file length does not
		 * include any CPMEOF (^Z) or other garbage characters used to pad the
		 * last block.
		 * The receiver stores the specified number of characters, discarding
		 * any padding added by the sender to fill up the last block.
		 */
		temp = "";
		while (i < packet.length) {
			byte b = packet[i];
			if ((b == 0x20) || (b == 0x00)) {
				i++;
				break;
			}
			temp += (char)b;
			i++;
		}
		try {
			download.length = Long.parseLong(temp);
		} catch (NumberFormatException e) {
			// just leave it at 0
		}
		if ((i >= packet.length) || (packet[i] == 0x00)) {
			return download;
		}
		
		// MODIFICATION TIME
		/*
		 * Chapter 5.  YMODEM Batch File Transmission
		 * The mod date is optional, and the filename and length
		 * may be sent without requiring the mod date to be sent.
		 * Iff the modification date is sent, a single space separates the
		 * modification date from the file length.
		 * The mod date is sent as an octal number giving the time the contents
		 * of the file were last changed, measured in seconds from Jan 1 1970
		 * Universal Coordinated Time (GMT).  A date of 0 implies the
		 * modification date is unknown and should be left as the date the file
		 * is received.
		 */
		temp = "";
		while (i < packet.length) {
			byte b = packet[i];
			if ((b == 0x20) || (b == 0x00)) {
				i++;
				break;
			}
			temp += (char)b;
			i++;
		}
		try {
			download.setFileTime(Long.parseLong(temp, 8));
		} catch (NumberFormatException e) {
			// just leave it at 0
		}
		if ((i >= packet.length) || (packet[i] == 0x00)) {
			return download;
		}
		
		// FILE MODE
		/*
		 * Chapter 5.  YMODEM Batch File Transmission
		 * Iff the file mode is sent, a single space separates the file mode
		 * from the modification date.  The file mode is stored as an octal
		 * string.  Unless the file originated from a Unix system, the file mode
		 * is set to 0.
		 */
		temp = "";
		while (i < packet.length) {
			byte b = packet[i];
			if ((b == 0x20) || (b == 0x00)) {
				i++;
				break;
			}
			temp += (char)b;
			i++;
		}
		try {
			download.mode = Integer.parseInt(temp, 8);
		} catch (NumberFormatException e) {
			// just leave it at 0
		}
		if ((i >= packet.length) || (packet[i] == 0x00)) {
			return download;
		}
		
		// SERIAL NUMBER
		/*
		 * Chapter 5.  YMODEM Batch File Transmission
		 * Iff the serial number is sent, a single space separates the
		 * serial number from the file mode.  The serial number of the
		 * transmitting program is stored as an octal string.  Programs which do
		 * not have a serial number should omit this field, or set it to 0.
		 */
		temp = "";
		while (i < packet.length) {
			byte b = packet[i];
			if ((b == 0x20) || (b == 0x00)) {
				i++;
				break;
			}
			temp += (char)b;
			i++;
		}
		try {
			download.serial = Integer.parseInt(temp, 8);
		} catch (NumberFormatException e) {
			// just leave it at 0
		}
		if ((i >= packet.length) || (packet[i] == 0x00)) {
			return download;
		}

		// OTHER FIELDS?
		/*
		 * Chapter 5.  YMODEM Batch File Transmission
		 * YMODEM was designed to allow additional header fields to be
		 * added as above without creating compatibility problems with older
		 * YMODEM programs.
		 * The rest of the block is set to nulls.  This is essential to preserve
		 * upward compatibility.
		 * If, perchance, this information extends beyond 128 bytes (possible
		 * with Unix 4.2 BSD extended file names), the block should be sent as a
		 * 1k block as described above.
		 */
		return download;
	}
	
	private void purge() throws UserCancelException {
		/*
		 * Chapter 7.4  Programming Tips
		 * The most common technique is for "PURGE" to call the character
		 * receive subroutine, specifying a 1-second timeout,[1] and looping
		 * back to PURGE until a timeout occurs.
		 */
		while (readData(1000) != null) {}
	}
	
	private void nak() throws UserCancelException {
		/*
		 * Chapter 7.3.2  Receive_Program_Considerations
		 * If the receiver wishes to <nak> a
		 * block for any reason (invalid header, timeout receiving data), it must
		 * wait for the line to clear.
		 */
		/*
		 * Chapter 7.4  Programming Tips
		 * When the receiver wishes to <nak>, it should call a "PURGE"
		 * subroutine, to wait for the line to clear.  Recall the sender tosses
		 * any characters in its UART buffer immediately upon completing sending
		 * a block, to ensure no glitches were mis- interpreted.
		 */
		purge();
		io.write(NAK);
	}
	
	private void cancel(String message) {
		io.log(message);
		try {
			purge();
		} catch (UserCancelException e) {
			// Swallow the exception... We are already cancelling!
		}
		/*
		 * Chapter 4.1  Graceful Abort
		 * YAM sends eight CAN
		 * characters when it aborts an XMODEM, YMODEM, or ZMODEM protocol file
		 * transfer.  Pro-YAM then sends eight backspaces to delete the CAN
		 * characters from the remote's keyboard input buffer, in case the remote had
		 * already aborted the transfer and was awaiting a keyboarded command.
		 */
		for (int i=0; i<8; i++) {
			io.write(CAN);
		}
		for (int i=0; i<8; i++) {
			io.write(BS);
		}
	}

	/**
	 * Waits for the next data byte.
	 * 
	 * @param timeout Milliseconds to wait before timing out.
	 * @return Next data byte, or null if timed out.
	 * @throws UserCancelException If user cancelled the download.
	 */
	private Character readData(int timeout) throws UserCancelException {
		if (waitingData != null) {
			char c = waitingData;
			waitingData = null;
			return c;
		}
		Byte b = io.read(timeout);
		return (b == null) ? null : (char)(b & 0xFF);
	}

	/**
	 * Waits for next data byte to be available.
	 * 
	 * @param timeout Milliseconds to wait before timing out.
	 * @return True if data byte is available, or null if timed out.
	 * @throws UserCancelException If user cancelled the download.
	 */
	private boolean waitForData(int timeout) throws UserCancelException {
		if (waitingData != null) {
			return true;
		}
		Byte b = io.read(timeout);
		waitingData = (b == null) ? null : (char)(b & 0xFF);
		return !(waitingData == null);
	}

	/**
	 * Retries the given code up to num times.
	 * 
	 * @param num Number of times to try
	 * @param supplier Code to run
	 * @return True if one of the attempts succeeded, false if all failed.
	 * @throws UserCancelException If user cancelled the download.
	 */
	private boolean retry(int num, Retrier retrier) throws UserCancelException {
		for (int i=0; i<num; i++) {
			if (retrier.attempt()) {
				return true;
			}
		}
		return false;
	}
	
	private interface Retrier {
		public boolean attempt() throws UserCancelException;
	}
	
	private static class ProtocolDetector {
		private enum Protocol {
			XModemChecksum ("XModem-Checksum"),
			XModemCRC ("XModem-CRC"),
			XModem1K ("XModem-1K"),
			YModemBatch ("YModem-Batch"),
			YModemG ("YModem-G");
			public final String label;
			private Protocol(String label) {
				this.label = label;
			}
		}
		private final List<Protocol> protocols;
		private final IOHandler io;
		private boolean reported = false;
		public boolean isCRC = false;
		public boolean isBatch = false;
		public boolean isStreaming = false;

		public ProtocolDetector(IOHandler ioHandler) {
			this.io = ioHandler;
			this.protocols = new ArrayList<>();
			this.protocols.addAll(Arrays.asList(Protocol.values()));
		}
		
		private void logProtocol() {
			if (!reported && (protocols.size() == 1)) {
				reported = true;
				io.log("Detected protocol: " + protocols.get(0).label);
			}
		}
		
		public void setCRC(boolean on) {
			if (on) {
				isCRC = true;
				protocols.remove(Protocol.XModemChecksum);
			} else {
				isCRC = false;
				protocols.remove(Protocol.XModemCRC);
				protocols.remove(Protocol.XModem1K);
				protocols.remove(Protocol.YModemBatch);
				protocols.remove(Protocol.YModemG);
			}
			logProtocol();
		}
		
		public void setStreaming(boolean on) {
			if (on) {
				isCRC = true;
				isStreaming = true;
				protocols.remove(Protocol.XModemChecksum);
				protocols.remove(Protocol.XModemCRC);
				protocols.remove(Protocol.XModem1K);
				protocols.remove(Protocol.YModemBatch);
			} else {
				isStreaming = false;
				protocols.remove(Protocol.YModemG);
			}
			logProtocol();
		}
		
		public void setBatch(boolean on) {
			if (on) {
				isBatch = true;
				protocols.remove(Protocol.XModemChecksum);
				protocols.remove(Protocol.XModemCRC);
				protocols.remove(Protocol.XModem1K);
			} else {
				isBatch = false;
				protocols.remove(Protocol.YModemBatch);
				protocols.remove(Protocol.YModemG);
			}
			logProtocol();
		}
		
		public void set1K(boolean on) {
			if (on) {
				protocols.remove(Protocol.XModemChecksum);
				protocols.remove(Protocol.XModemCRC);
			} else {
				protocols.remove(Protocol.XModem1K);
				protocols.remove(Protocol.YModemBatch);
				protocols.remove(Protocol.YModemG);
			}
			logProtocol();
		}
	}
}

/*
***zmodem start***

[G]
**B00000000000000

[]


*/

