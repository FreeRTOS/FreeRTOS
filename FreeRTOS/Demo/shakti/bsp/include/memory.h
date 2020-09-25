/***************************************************************************
 * Project           		: shakti devt board
 * Name of the file	     	: memory.h
 * Brief Description of file    : dumps values at memory mapped locations,useful for debugging 
 * Name of Author    	        : Sathya Narayanan N 
 * Email ID                     : sathya281@gmail.com

 Copyright (C) 2019  IIT Madras. All rights reserved.

 This program is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program.  If not, see <https://www.gnu.org/licenses/>.
 ***************************************************************************/
 /**
 * @file memory.h
 * @brief dumps values at memory mapped locations, useful for debugging 
 */

void dump_word_memory(uint32_t* start, uint32_t word_length);
void dump_byte_memory(uint32_t* start, uint32_t word_length);

