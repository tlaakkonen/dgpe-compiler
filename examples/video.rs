trait IntoFrame {
    fn frame_size(&self) -> (usize, usize);
    fn make_frame(&self) -> video_rs::frame::RawFrame;
}

impl IntoFrame for dgpe::dist::BlockMatrix {
    fn frame_size(&self) -> (usize, usize) {
        (2*self.qubits + 32, 2*self.qubits + 32)
    }

    fn make_frame(&self) -> video_rs::frame::RawFrame {
        let mut frame = video_rs::frame::RawFrame::new(video_rs::frame::PixelFormat::RGB24, 2*self.qubits as u32 + 32, 2*self.qubits as u32 + 32);
        let data = frame.plane_mut::<[u8; 3]>(0);
        for y in 0..2*self.qubits + 32 {
            for x in 0..2*self.qubits + 32 {
                let c = if x >= 16 && x < 2*self.qubits + 16 && y >= 16 && y < 2*self.qubits + 16 {
                    255 * (!bool::from(self.mat[((y - 16)/2, (x - 16)/2)]) as u8)
                } else {
                    255
                };
                data[y*(2*self.qubits + 32) + x] = [c, c, c];
            }
        }    
        frame
    }
}

impl IntoFrame for dgpe::dist::BlockTableau {
    fn frame_size(&self) -> (usize, usize) {
        (4*self.qubits + 32, 4*self.qubits + 32)
    }

    fn make_frame(&self) -> video_rs::frame::RawFrame {
        let mut frame = video_rs::frame::RawFrame::new(video_rs::frame::PixelFormat::RGB24, 4*self.qubits as u32 + 32, 4*self.qubits as u32 + 32);
        let data = frame.plane_mut::<[u8; 3]>(0);
        for y in 0..4*self.qubits + 32 {
            for x in 0..4*self.qubits + 32 {
                let (r, g, b) = if x >= 16 && x < 4*self.qubits + 16 && y >= 16 && y < 4*self.qubits + 16 {
                    let row = ((y - 16) / 2) % self.qubits;
                    let col = ((x - 16) / 2) % self.qubits;
                    let row_part = self.indices.iter().rposition(|&s| s <= row).unwrap();
                    let row_offset = row - self.indices[row_part];
                    let stab = self.stabs[row_part][col].get(row_offset);
                    let destab = self.destabs[row_part][col].get(row_offset);
                    let p = if (x - 16) < 2*self.qubits { stab } else { destab };
                    let c = p == dgpe::Pauli::Y || if (y - 16) < 2*self.qubits { p == dgpe::Pauli::Z } else { p == dgpe::Pauli::X };
                    (255 * (!c as u8), 255 * (!c as u8), 255 * (!c as u8))
                } else {
                    (255, 255, 255)
                };
                data[y*(4*self.qubits + 32) + x] = [r, g, b];
            }
        }    
        frame
    }
}

fn main() {
    struct Rec<R> {
        rep: R,
        encoder: video_rs::encode::Encoder,
        duration: video_rs::time::Time,
        position: video_rs::time::Time,
        count: usize
    }

    impl<R: IntoFrame> Rec<R> {
        fn encode_frame(&mut self) {
            println!("{:?}", self.count);
            let mut frame = self.rep.make_frame();
            frame.set_pts(self.position.with_time_base(self.encoder.time_base()).into_value());
            self.encoder.encode_raw(frame).unwrap();
            self.position = self.position.aligned_with(self.duration).add();
            self.count += 1;
        }
    }

    impl<R: IntoFrame + dgpe::dist::NonlocalRecorder> dgpe::dist::NonlocalRecorder for Rec<R> {
        fn nonlocal_exp(&mut self, exp: &dgpe::NonlocalExp) {
            self.rep.nonlocal_exp(exp);
            self.encode_frame();
        }
    } 
    

    let circ = dgpe::Circuit::random_clifford(256, 32768, 0.1, 0.1);
    let mut tableau = dgpe::CliffordBasis::from_circuit(&circ).unwrap();
    // let mut parity = tableau.to_parity_matrix().unwrap();
    let arch = dgpe::GlobalArch::all_to_all(16, 16);
    let block = dgpe::dist::BlockTableau::new(&tableau, &arch);
    // let block = dgpe::dist::BlockMatrix::new(&parity, &arch);

    video_rs::init().unwrap();
    let (width, height) = block.frame_size();
    let settings = video_rs::encode::Settings::preset_h264_yuv420p(width, height, false);
    let mut encoder = video_rs::encode::Encoder::new(std::path::Path::new("videos/clifford_recursive.mp4"), settings).expect("failed to create encoder");
    let duration = video_rs::time::Time::from_nth_of_a_second(120);
    let mut position = video_rs::time::Time::zero();

    for k in [2, 4, 8, 16, 32, 64, 128, 256] {
        let arch = dgpe::GlobalArch::all_to_all(k, 256 / k);
        let mut block = dgpe::dist::BlockTableau::new(&tableau, &arch);

        let mut rec = Rec { rep: block.clone(), encoder, duration, position, count: 0 };
        block.synthesize(&mut rec);
        if k == 256 {
            rec.encode_frame();
            rec.encode_frame();
        }
        encoder = rec.encoder;
        position = rec.position;
        tableau = block.to_tableau();
    }
    encoder.finish().unwrap();
}

