/*****************************************************************************************[system.rs]
Copyright (c) 2018-2018, Masaki Hara

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

use cpu_time::ProcessTime;

#[derive(Debug)]
pub(crate) struct ResourceMeasure {
    start: ProcessTime,
}

impl ResourceMeasure {
    pub(crate) fn new() -> ResourceMeasure {
        ResourceMeasure { start: ProcessTime::now() }
    }

    pub fn cpu_time(&self) -> f64 {
        let dur = ProcessTime::now().duration_since(self.start);
        dur.as_secs() as f64 + (dur.subsec_millis() as f64 / 1000.)
    }

    /* TODO
    pub fn mem_used_peak(&self) -> f64 {
        0.0
    }
    */
}

