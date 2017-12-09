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

/**
 * Interface for handling various events during a download.
 * 
 * @author walton
 */
public interface IOHandler {
	/**
	 * Called during download to read the next input byte.
	 * <p>
	 * Blocks until the next byte is available.
	 * If timeout is reached, return null.
	 * If user cancels the download while blocked, throw DownloadCancelException.
	 * 
	 * @param msTimeout Milliseconds to wait before timing out.
	 * @return Next data byte, or null if timed out.
	 * @throws UserCancelException If user cancelled the download.
	 */
	public Byte read(int msTimeout) throws UserCancelException;
	/**
	 * Called during download to send a byte to the sender.
	 * 
	 * @param ch Byte to transmit.
	 */
	public void write(char ch);
	/**
	 * Called during download with logging messages.
	 * 
	 * @param message Message to log.
	 */
	public void log(String message);
	/**
	 * Called during download with progress data.
	 * 
	 * @param bytes Number of bytes downloaded so far.
	 * @param total Total size of file being downloaded (0 if unknown).
	 */
	public void progress(long bytes, long total);
	/**
	 * Called at end of successful download with details of downloaded file.
	 * 
	 * @param download Download object with details of downloaded file, including a reference to it.
	 */
	public void received(Download download);
}
